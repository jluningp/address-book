{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-}

module Handler.Browse where

import Import
import BinahLibrary hiding (filter)

processPeople :: [(PersonId, Person)] -> Handler [(Entity Person, Bool, Bool)]
processPeople peopleList = do
  authPerson <- Import.getAuthPerson
  people <- case authPerson of
              Nothing -> return $ map (\(id, x) -> (Entity id x, False, False)) peopleList
              Just (pid, _) -> do
                friendList <- Import.getFriendList pid
                requestList <- Import.getOutgoingRequestList pid
                mapM (\(id, Person email name street number) -> do
                        me <- Import.isMe id
                        return $ let e = pack email in
                                   (Entity id (Person email name street number),
                                    any (\y -> y == e) friendList || me,
                                    any (\y -> y == e) requestList || me)) peopleList
  return people

getBrowseR :: Handler Html
getBrowseR = do
  peopleList <- runDB $ selectList [] [Asc PersonName]
  peopleTupleList <- return $ map (\(Entity id p) -> (id, p)) peopleList
  people <- processPeople peopleTupleList
  defaultLayout $(widgetFile "browse")


getAuthPerson :: Handler (Maybe (Key Person, Person))
getAuthPerson = do
    myId <- maybeAuthId
    authPerson <- case myId of
                   Nothing -> return $ Nothing
                   Just id -> runDB $ do
                     user <- get id
                     authPerson <-
                       case user of
                         Nothing -> return $ Nothing
                         Just u -> do
                           x <- getBy $ UniquePerson (userEmail u)
                           authPerson <- case x of
                                           Nothing -> return $ Nothing
                                           Just (Entity uid person) -> return $ Just (uid, person)
                           return authPerson
                     return authPerson
    return authPerson


getAddFriendR :: PersonId -> Handler Html
getAddFriendR personId = do
  Person email name street number <- runDB $ get404 personId
  authPerson <- Import.getAuthPerson
  case authPerson of
    Nothing -> redirect HomeR --will change
    Just (myId, Person myEmail _ _ _) -> runDB $ do
      theirFriends <- getBy $ UniqueFriend email
      myFriends <- getBy $ UniqueFriend myEmail
      case theirFriends of
        Nothing -> do
          insert $ Friends email [myEmail] [] []
          return ()
        Just (Entity uid (Friends _ requests friendList _)) -> refinedUpdate uid [FriendsRequests =# (myEmail:requests)]
      case myFriends of
        Nothing -> do
          insert $ Friends myEmail [] [] [email]
          return ()
        Just (Entity uid (Friends _ _ _ outgoing)) -> refinedUpdate uid [FriendsOutgoingRequests =# (email:outgoing)]
  redirect $ BrowseR

getConfirmFriendR :: PersonId -> Handler Html
getConfirmFriendR personId = do
  Person email name street number <- runDB $ get404 personId
  authPerson <- Import.getAuthPerson
  case authPerson of
    Nothing -> redirect HomeR --will change
    Just (myId, Person myEmail _ _ _) -> runDB $ do
      theirFriends <- getBy $ UniqueFriend email
      myFriends <- getBy $ UniqueFriend myEmail
      case theirFriends of
        Nothing -> do
          insert $ Friends email [] [myEmail] []
          return ()
        Just (Entity uid (Friends _ requests friendList _)) ->
          refinedUpdate uid [FriendsFriends =# (myEmail:friendList),
                             FriendsOutgoingRequests =# (filter (\x -> x /= myEmail) requests)]
      case myFriends of
       Nothing -> do
         insert $ Friends myEmail [] [email] []
         return ()
       Just (Entity uid (Friends _ _ friendList outgoing)) ->
         refinedUpdate uid [FriendsFriends =# (email:friendList),
                            FriendsRequests =# (filter (\x -> x /= email) outgoing)]

  redirect $ ProfileR personId
