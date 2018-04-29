{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

--{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
--{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}

module Handler.Browse where

import Import
import qualified Queries
import BinahLibrary hiding (filter)
import Data.Traversable
import qualified Data.Maybe as Maybe

processPeople :: Tagged [(PersonId, Person)] -> Handler (Tagged (Handler (Tagged [(Entity Person, Bool, Bool)])))
processPeople peopleList = do
  authPersonTagged <- Queries.getAuthPerson
  friends <- return $ do --Tagged Handler (Maybe Tagged)
    authPerson <- authPersonTagged
    case authPerson of
      Nothing -> return $ return Nothing
      Just (pid, _) -> return $ do
        friendList <- Queries.getFriendList pid
        requestList <- Queries.getOutgoingRequestList pid
        return $ Just (friendList, requestList)
  people <- return $ do
    hmt <- friends
    return $ do
      mt <- hmt
      case mt of
        Nothing -> return $ fmap (map (\(id, x) -> (Entity id x, False, False))) peopleList
        Just (friendListT, requestListT) ->
          return $ do
          pList <- peopleList
          friendList <- friendListT
          requestList <- requestListT
          return $ map (\(id, Person email name street number ) ->
                           let e = pack email
                           in
                             (Entity id (Person email name street number),
                               any (\y -> y == e) friendList,
                               any (\y -> y == e) requestList)) pList
  return $ people

getBrowseR :: Handler Html
getBrowseR = do
  user <- Handler.Browse.getAuthUser
  personT <- Queries.getAuthPerson
  peopleDetailsTH <- return $ do
    person <- personT
    (_, Person _ name _ _) <- return $ Maybe.fromJust person
    return $ do
      peopleList <- runDB $ (selectPerson ([filterPersonName NE name]) [Asc PersonName])
      peopleTHT <- let peopleTupleList = fmap (map (\(Entity id p) -> (id, p))) peopleList
                 in processPeople peopleTupleList
      peopleT <- safeUnwrap peopleTHT user
      peopleDetails <- return $  map (\(Entity id (Person _ name _ _), a, b) -> (id, name, a, b))
                       (safeUnwrap peopleT user)
      return peopleDetails
  peopleDetails <- safeUnwrap peopleDetailsTH user
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
  user <- Handler.Browse.getAuthUser
  authPersonT <- Queries.getAuthPerson
  listsTHMT <- return $ do
    authPerson <- authPersonT
    case authPerson of
      Nothing -> return $ return $ Nothing
      Just (myId, Person myEmail _ _ _) ->
        return $ runDB $ do
           theirFriends <- selectFriends [filterFriendsEmail EQUAL email] []
           myFriends <- selectFriends [filterFriendsEmail EQUAL myEmail] []
           return $ Just (theirFriends, myFriends, myEmail)

  listsMT <- safeUnwrap listsTHMT user
  case listsMT of
    Nothing -> redirect HomeR --will change
    Just (theirFriendsT, myFriendsT, myEmail) ->
      let theirFriends = safeUnwrap theirFriendsT user
          myFriends = safeUnwrap myFriendsT user in
        runDB $ do
        case theirFriends of
          [] -> do
            insert $ Friends email [myEmail] [] []
            return ()
          (Entity uid (Friends _ requests friendList _)):_ ->
            refinedUpdate uid [FriendsRequests =# (myEmail:requests)]
        case myFriends of
          [] -> do
            insert $ Friends myEmail [] [] [email]
            return ()
          (Entity uid (Friends _ _ _ outgoing)):_ ->
            refinedUpdate uid [FriendsOutgoingRequests =# (email:outgoing)]
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
