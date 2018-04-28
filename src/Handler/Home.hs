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

getPersonDetails :: String -> Handler (Tagged (PersonId, Person))
getPersonDetails email = do
  maybePersonTagged <- runDB $ selectPerson [filterPersonEmail EQUAL email] []
  return $ do
    maybePerson <- maybePersonTagged
    return $ case maybePerson of
               [] -> error "aaaa" -- Can't occur
               (Entity uid person):_ -> (uid, person)

getFriendPrintout :: Maybe User -> Tagged (PersonId, Person) -> String
getFriendPrintout maybeUser taggedPerson =
  case maybeUser of
    Nothing -> ""
    Just user ->
      let (_, Person _ name street number) = safeUnwrap taggedPerson user in
        name ++ (fromString ": ") ++ (fromString (show number)) ++ (fromString " ") ++ street

getRequestPrintout :: User -> Tagged (PersonId, Person) -> (PersonId, String)
getRequestPrintout user taggedPerson =
  let (pid, Person _ name _ _) = safeUnwrap taggedPerson user
  in (pid, name)

getConfirmLinkR :: String -> Handler Html
getConfirmLinkR link = do
  defaultLayout $ do
    setTitle "Create Account"
    $(widgetFile "showlink")


getHomeR :: Handler Html
getHomeR = do
    myId <- maybeAuthId
    maybePersonTagged <- getAuthPerson
    maybeUser <- getAuthUser
    loggedIn <- return $ case maybeUser of
                           Nothing -> False
                           Just user -> case safeUnwrap maybePersonTagged user of
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
    friendEmailListTaggedHandlerTagged <- return $ do
      maybePerson <- maybePersonTagged
      return $ case maybePerson of
                 Just (pid, _) -> Import.getFriendList pid
                 Nothing -> return $ return []
    requestEmailListTaggedHandlerTagged <- return $ do
      maybePerson <- maybePersonTagged
      return $ case maybePerson of
                 Just (pid, _) -> Import.getRequestList pid
                 Nothing -> return $ return []
    friendPersonList <- return $ do --handler   :: Tagged (Handler (Tagged (Handler [Tagged])))
      friendEmailListHandlerTagged <- friendEmailListTaggedHandlerTagged
      return $ do --tagged
        friendEmailListTagged <- friendEmailListHandlerTagged
        return $ do --handler
          friendEmailList <- friendEmailListTagged
          return {-tagged-} $ mapM getPersonDetails $ map unpack friendEmailList --[handler tagged]
    requestPersonList <- return $ do --handler   :: Tagged (Handler (Tagged (Handler [Tagged])))
      requestEmailListHandlerTagged <- requestEmailListTaggedHandlerTagged
      return $ do --tagged
        requestEmailListTagged <- requestEmailListHandlerTagged
        return $ do --handler
          requestEmailList <- requestEmailListTagged
          return {-tagged-} $ mapM getPersonDetails $ map unpack requestEmailList
    friendListTHTHL <- return $ fmap (\hthl -> fmap (\thl -> fmap (\hl -> fmap (\l ->
                           map (getFriendPrintout maybeUser) l) hl) thl) hthl) friendPersonList
    requestListTHTHL <- return $ fmap (\hthl -> fmap (\thl -> fmap (\hl -> fmap (\l ->
                            case maybeUser of
                              Nothing -> []
                              Just user -> map (getRequestPrintout user) l) hl) thl) hthl) requestPersonList
    friendListH <- case maybeUser of
                       Nothing -> return $ return []
                       Just user -> return $ do
                         friendListTHL <- safeUnwrap friendListTHTHL user
                         friendList <- safeUnwrap friendListTHL user
                         return friendList
    friendList <- friendListH

    requestListH <- case maybeUser of
                       Nothing -> return $ return []
                       Just user -> return $ do
                         requestListTHL <- safeUnwrap requestListTHTHL user
                         requestList <- safeUnwrap requestListTHL user
                         return requestList
    requestList <- requestListH

    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Welcome To Yesod!"
        $(widgetFile "homepage")
