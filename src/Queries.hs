{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}

module Queries where

import Import hiding (getAuthUser, getAuthPerson, getList, getFriendList, getRequestList,
                      getOutgoingRequestList, isInList, isFriend, isFriendRequest, isMe)
import Yesod.Default.Util   (addStaticContentExternal)
import Yesod.Core.Types     (Logger)
import Data.Maybe
import BinahLibrary
import TaggedUser
import TaggedEmail
import TaggedPerson
import TaggedFriends


getAuthUser :: Handler (Maybe User)
getAuthUser = do
  myId <- maybeAuthId
  authUser <- case myId of
                Nothing -> return Nothing
                Just id -> runDB $ do
                  userOpt <- get id
                  return $ userOpt
  return authUser

{-@ getAuthPerson :: Handler (TaggedPerson<{\r u -> isVerified u}> (Maybe (Key Person, Person))) @-}
getAuthPerson :: Handler (TaggedPerson (Maybe (Key Person, Person)))
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


{-@ getList :: (Friends -> [String]) -> PersonId -> Handler (TaggedFriends<{\u -> True}> ([Text], Maybe Friends)) @-}
getList :: (Friends -> [String]) -> PersonId -> Handler (TaggedFriends ([Text], Maybe Friends))
getList getter personId = do
  personOpt <- runDB $ get personId
  list <- case personOpt of
            Nothing -> return $ return ([], Nothing)
            Just (Person email _ _ _) ->
              runDB $ do
              friendsOpt <- selectFriends [filterFriendsEmail EQUAL email] []
              return $ fmap (\friends -> case friends of
                                           [] -> ([], Nothing)
                                           (Entity uid friend):_ ->
                                             (map pack (getter friend), Just friend)) friendsOpt
  return list


{-@ getFriendList :: PersonId -> Handler (TaggedFriends<{\u -> True}> ([Text], Maybe Friends)) @-}
getFriendList :: PersonId -> Handler (TaggedFriends ([Text], Maybe Friends))
getFriendList = getList friendsFriends
{-@ getRequestList :: PersonId -> Handler (TaggedFriends<{\u -> True}> ([Text], Maybe Friends)) @-}
getRequestList :: PersonId -> Handler (TaggedFriends ([Text], Maybe Friends))
getRequestList = getList friendsRequests
{-@ getOutgoingRequestList :: PersonId -> Handler (TaggedFriends<{\u -> True}> ([Text], Maybe Friends)) @-}
getOutgoingRequestList :: PersonId -> Handler (TaggedFriends ([Text], Maybe Friends))
getOutgoingRequestList = getList friendsOutgoingRequests

{-@ isMe :: PersonId -> Handler (TaggedPerson<{\u -> isVerified u}> (Bool, Maybe Person)) @-}
isMe :: PersonId -> Handler (TaggedPerson (Bool, Maybe Person))
isMe personId = do
    muid <- maybeAuthId
    pidTagged <- getAuthPerson
    return $ do
      pid <- pidTagged
      return $ case muid of
                 Nothing -> (False, Nothing)
                 Just id -> case pid of
                              Nothing -> (False, Nothing)
                              Just (pid, person) -> do
                                if pid == personId
                                  then (True, Just person)
                                  else (False, Just person)
