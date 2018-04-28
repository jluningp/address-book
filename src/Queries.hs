{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-@ LIQUID "--exact-data-con"                      @-}

module Queries where
{-
import Import hiding (getAuthUser, getAuthPerson, getList, getFriendList, getRequestList,
                      getOutgoingRequestList, isInList, isFriend, isFriendRequest, isMe)
import Yesod.Default.Util   (addStaticContentExternal)
import Yesod.Core.Types     (Logger)
import Data.Maybe
import BinahLibrary


getAuthUser :: Handler (Maybe User)
getAuthUser = do
  myId <- maybeAuthId
  authUser <- case myId of
                Nothing -> return Nothing
                Just id -> runDB $ do
                  userOpt <- get id
                  return $ userOpt
  return authUser

{-@ getSomething :: Handler (Tagged<{\u -> isVerified u}> [Entity Person]) @-}
getSomething :: Handler (Tagged [Entity Person])
getSomething = do
  people <- runDB $ selectPerson [filterPersonEmail EQUAL "FOO"] []
  return people

-- Ignore the code below: if it isn't there, the project won't build, but we needed
-- a simple example so I made it undefined.

{-@ getAuthPerson :: Handler (Tagged<{\u -> isVerified u}> (Maybe (Key Person, Person))) @-}
getAuthPerson :: Handler (Tagged (Maybe (Key Person, Person)))
getAuthPerson = do
  myId <- maybeAuthId
  authPerson <- case myId of
                  Nothing -> return $ return Nothing
                  Just id -> runDB $ do
                    userOpt <- get id
                    user <- return $ fromJust userOpt
                    entityPersonTagged <- selectPerson [filterPersonEmail EQUAL (userEmail user)] []
                    return $ do
                      entityPerson <- entityPersonTagged
                      return $ case entityPerson of
                                 [] -> Nothing
                                 (Entity uid person):_ -> Just (uid, person)
  return authPerson


{-@ getList :: (Friends -> [String]) -> PersonId -> Handler (Tagged<{\u -> isVerified u}> [Text]) @-}
getList :: (Friends -> [String]) -> PersonId -> Handler (Tagged [Text])
getList getter personId = do
  personOpt <- runDB $ get personId
  list <- case personOpt of
            Nothing -> return $ return []
            Just (Person email _ _ _) ->
              runDB $ do
              friendsOpt <- selectFriends [filterFriendsEmail EQUAL email] []
              return $ fmap (\friends -> case friends of
                                           [] -> []
                                           (Entity uid friend):_ ->
                                             map pack (getter friend)) friendsOpt
  return list


{-@ getFriendList :: PersonId -> Handler (Tagged<{\u -> isVerified u}> [Text]) @-}
getFriendList :: PersonId -> Handler (Tagged [Text])
getFriendList = getList friendsFriends
{-@ getRequestList :: PersonId -> Handler (Tagged<{\u -> isVerified u}> [Text]) @-}
getRequestList :: PersonId -> Handler (Tagged [Text])
getRequestList = getList friendsRequests
{-@ getOutgoingRequestList :: PersonId -> Handler (Tagged<{\u -> isVerified u}> [Text]) @-}
getOutgoingRequestList :: PersonId -> Handler (Tagged [Text])
getOutgoingRequestList = getList friendsOutgoingRequests

{-@ isInList :: (PersonId -> Handler (Tagged [Text])) -> PersonId -> Handler (Tagged<{\u -> isVerified u}> (Handler (Tagged<{\u -> isVerified u}> Bool))) @-}
isInList :: (PersonId -> Handler (Tagged [Text])) -> PersonId -> Handler (Tagged (Handler (Tagged Bool)))
isInList getter p2 = do --Tagged
  muid <- maybeAuthId
  pidTagged <- getAuthPerson
  person2Opt <- runDB $ get p2
  return $ do -- Tagged
    pid <- pidTagged
    case pid of
      Nothing -> return $ ((return $ return False) :: Handler (Tagged Bool))
      Just (p1, Person email1 _ _ _) -> return $ do --Handler
        friendListTagged <- getter p1
        return $ do --Tagged
          friendList <- friendListTagged
          return $ case person2Opt of
                     Nothing -> False
                     Just (Person email2 _ _ _) -> let e2 = pack email2
                                                   in any (\x -> e2 == x) friendList


{-@ isFriend :: PersonId -> Handler (Tagged<{\u -> isVerified u}> (Handler (Tagged<{\u -> isVerified u}> Bool))) @-}
isFriend :: PersonId -> Handler (Tagged (Handler (Tagged Bool)))
isFriend = isInList getFriendList

{-@ isFriendRequest :: PersonId -> Handler (Tagged<{\u -> isVerified u}> (Handler (Tagged<{\u -> isVerified u}> Bool))) @-}
isFriendRequest :: PersonId -> Handler (Tagged (Handler (Tagged Bool)))
isFriendRequest = isInList getRequestList

{-@ isMe :: PersonId -> Handler (Tagged<{\u -> isVerified u}> Bool) @-}
isMe :: PersonId -> Handler (Tagged Bool)
isMe personId = do
    muid <- maybeAuthId
    pidTagged <- getAuthPerson
    return $ do
      pid <- pidTagged
      case muid of
        Nothing -> return False
        Just id -> case pid of
                     Nothing -> return False
                     Just (pid, _) -> do
                       if pid == personId
                         then return True
                         else return False
-}
