{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Home where

import Import
import BinahLibrary
import Yesod.Form.Bootstrap3 (BootstrapFormLayout (..), renderBootstrap3)
import Text.Julius (RawJS (..))

-- Define our data that will be used for creating the form.
data FileForm = FileForm
    { fileInfo :: FileInfo
    , fileDescription :: Text
    }

-- This is a handler function for the GET request method on the HomeR
-- resource pattern. All of your resource patterns are defined in
-- config/routes
--
-- The majority of the code you will write in Yesod lives in these handler
-- functions. You can spread them across multiple files if you are so
-- inclined, or create a single monolithic file.

getPersonDetails :: String -> Handler (Maybe (PersonId, Person))
getPersonDetails email = do
  maybePerson <- runDB $ getBy $ UniquePerson email
  case maybePerson of
    Nothing -> return Nothing
    Just (Entity uid person) -> return $ Just (uid, person)

getFriendPrintout :: Maybe (PersonId, Person) -> String
getFriendPrintout maybePerson =
  case maybePerson of
    Nothing -> ""
    Just (_, Person _ name street number) -> name ++ (fromString ": ") ++ (fromString (show number)) ++ (fromString " ") ++ street

getRequestPrintout :: (PersonId, Person) -> (PersonId, String)
getRequestPrintout (pid, Person _ name _ _) = (pid, name)

getConfirmLinkR :: String -> Handler Html
getConfirmLinkR link = do
  defaultLayout $ do
    setTitle "Create Account"
    $(widgetFile "showlink")


getHomeR :: Handler Html
getHomeR = do
    myId <- maybeAuthId
    maybePerson <- getAuthPerson
    maybeUser <- getAuthUser
    loggedIn <- return $ case maybeUser of
                           Nothing -> False
                           Just user -> case safeUnwrap maybePerson user of
                                          Nothing -> False
                                          Just _ -> True
    link <- case myId of
              Nothing -> return $ AuthR LoginR
              Just id -> runDB $ do
                user <- get id
                route <-
                  case user of
                           Nothing -> return $ AuthR LoginR
                           Just u -> do
                             x  <- getBy $ UniquePerson (userEmail u)
                             route <- case x of
                                        Nothing -> return $ AuthR LoginR
                                        Just (Entity uid _) -> return $ ProfileR uid
                             return route
                return route
    friendEmailList <- return ([] :: [String]) --case maybePerson of
                       --  Just (pid, _) -> Import.getFriendList pid
                       --  Nothing -> return []
    requestEmailList <- return ([] :: [String]) --case maybePerson of
                          --Just (pid, _) -> Import.getRequestList pid
                          --Nothing -> return []
    friendPersonList <-  mapM getPersonDetails $ map unpack (friendEmailList :: [String])
    requestMaybePersonList <- mapM getPersonDetails $ map unpack requestEmailList
    requestPersonList <- return $ mapMaybe (\x -> x) requestMaybePersonList
    friendList <- return $ map getFriendPrintout friendPersonList
    requestList <- return $ map getRequestPrintout requestPersonList
    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Welcome To Yesod!"
        $(widgetFile "homepage")
