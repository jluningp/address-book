{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Home where

import Import
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



getAuthPerson :: Handler (Maybe (Key Person, Person))
getAuthPerson = do
  myId <- maybeAuthId
  route <- case myId of
             Nothing -> return $ Nothing
             Just id -> runDB $ do
               user <- get id
               route <- 
                  case user of
                    Nothing -> return $ Nothing
                    Just u -> do 
                      x <- getBy $ UniquePerson (userEmail u)
                      route <- case x of
                                 Nothing -> return $ Nothing
                                 Just (Entity uid person) -> return $ Just (uid, person)
                      return route
               return route
  return route
    

getPersonDetails :: Text -> Handler (Maybe (PersonId, Person))
getPersonDetails email = do
  maybePerson <- runDB $ getBy $ UniquePerson email
  case maybePerson of
    Nothing -> return Nothing
    Just (Entity uid person) -> return $ Just (uid, person)

getFriendPrintout :: Maybe (PersonId, Person) -> Text
getFriendPrintout maybePerson =
  case maybePerson of
    Nothing -> ""
    Just (_, Person _ name street number) -> name ++ (fromString ": ") ++ (fromString (show number)) ++ (fromString " ") ++ street 

getRequestPrintout :: (PersonId, Person) -> (PersonId, Text)
getRequestPrintout (pid, Person _ name _ _) = (pid, name)

getConfirmLinkR :: Text -> Handler Html
getConfirmLinkR link = do
  defaultLayout $ do 
    setTitle "Create Account"
    $(widgetFile "showlink")
  

getHomeR :: Handler Html
getHomeR = do
    myId <- maybeAuthId
    maybePerson <- Import.getAuthPerson
    loggedIn <- case maybePerson of
                  Nothing -> return False
                  Just _ -> return True
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
    friendEmailList <- case maybePerson of
                         Just (pid, _) -> Import.getFriendList pid
                         Nothing -> return []

    requestEmailList <- case maybePerson of
                          Just (pid, _) -> Import.getRequestList pid
                          Nothing -> return []
    friendPersonList <- mapM getPersonDetails friendEmailList
    requestMaybePersonList <- mapM getPersonDetails requestEmailList
    requestPersonList <- return $ mapMaybe (\x -> x) requestMaybePersonList
    friendList <- return $ map getFriendPrintout friendPersonList
    requestList <- return $ map getRequestPrintout requestPersonList
    defaultLayout $ do
        let (commentFormId, commentTextareaId, commentListId) = commentIds
        aDomId <- newIdent
        setTitle "Welcome To Yesod!"
        $(widgetFile "homepage")

sampleForm :: Form FileForm
sampleForm = renderBootstrap3 BootstrapBasicForm $ FileForm
    <$> fileAFormReq "Choose a file"
    <*> areq textField textSettings Nothing
    -- Add attributes like the placeholder and CSS classes.
    where textSettings = FieldSettings
            { fsLabel = "What's on the file?"
            , fsTooltip = Nothing
            , fsId = Nothing
            , fsName = Nothing
            , fsAttrs =
                [ ("class", "form-control")
                , ("placeholder", "File description")
                ]
            }

commentIds :: (Text, Text, Text)
commentIds = ("js-commentForm", "js-createCommentTextarea", "js-commentList")
