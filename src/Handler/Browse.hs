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
import Data.Traversable
import qualified Data.Maybe as Maybe

processPeople :: Tagged [(PersonId, Person)] -> Handler (Tagged [(Entity Person, Bool, Bool)])
processPeople peopleList = do
  authPerson <- return Nothing --Import.getAuthPerson
  friends <- case authPerson of
                Nothing -> return Nothing
                Just (pid, _) -> do
                  friendList <- return ([] :: [String])--Import.getFriendList pid
                  requestList <- return ([] :: [String])--Import.getOutgoingRequestList pid
                  return $ Just (friendList, requestList, pid)
  people <- case friends of
              Nothing -> return $ fmap (map (\(id, x) -> (Entity id x, False, False))) peopleList
              Just (friendList, requestList, me) ->
                return $ fmap (map (\(id, Person email name street number) ->
                                      let e = pack email
                                      in
                                        (Entity id (Person email name street number),
                                         any (\y -> y == e) friendList,
                                         any (\y -> y == e) requestList))) peopleList
  return $ people

getBrowseR :: Handler Html
getBrowseR = do
  user <- Handler.Browse.getAuthUser
  person <- return Nothing--getAuthPerson
  (_, Person _ name _ _) <- return $ Maybe.fromJust person
  peopleList <- runDB $ (selectPerson ([filterPersonName NE name] {-:: [RefinedFilter Person String] -}) [Asc PersonName])
  people <- let peopleTupleList = fmap (map (\(Entity id p) -> (id, p))) peopleList
            in processPeople peopleTupleList
  peopleDetails <- return $ fmap (map (\(Entity id (Person _ name _ _), a, b) -> (id, name, a, b))) people
  defaultLayout $(widgetFile "browse")

getAuthUser :: Handler User
getAuthUser = do
  id <- maybeAuthId
  user <- runDB $ do
    usr <- get404 (Maybe.fromJust id)
    return usr
  return user


getAddFriendR :: PersonId -> Handler Html
getAddFriendR personId = do
  Person email name street number <- runDB $ get404 personId
  authPerson <- return Nothing --Import.getAuthPerson
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
  authPerson <- return Nothing --Import.getAuthPerson
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
