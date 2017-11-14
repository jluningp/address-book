{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Browse where

import Import

getBrowseR :: Handler Html
getBrowseR = do
  peopleList <- runDB $ selectList [] [Asc PersonName]
  authPerson <- Import.getAuthPerson
  people <- case authPerson of
              Nothing -> return $ map (\x -> (x, False)) peopleList
              Just (pid, _) -> do
                friendList <- Import.getFriendList pid
                mapM (\(Entity x (Person email name street number)) -> do
                        me <- Import.isMe x 
                        return $ (Entity x (Person email name street number),
                                  any (\y -> y == email || me) friendList)) peopleList 
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
      myFriends <- getBy $ UniqueFriend myEmail
      case myFriends of
        Nothing -> do
          insert $ Friends myEmail [email]
          return ()
        Just (Entity uid (Friends _ friendList)) -> update uid [FriendsFriends =. (email:friendList)]
  redirect $ ProfileR personId
