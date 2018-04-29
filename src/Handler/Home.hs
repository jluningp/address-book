{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}

module Handler.Home where

import Import
import BinahLibrary
import Queries
import Yesod.Form.Bootstrap3 (BootstrapFormLayout (..), renderBootstrap3)
import Text.Julius (RawJS (..))
import qualified Data.Maybe as Maybe

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

{-@ assume Prelude.error :: String -> a @-}

{-@ getPersonDetails :: String -> Handler (Tagged<{\u -> isVerified u}> (PersonId, Person)) @-}
getPersonDetails :: String -> Handler (Tagged (PersonId, Person))
getPersonDetails email = do
  maybePersonTagged <- runDB $ selectPerson ([filterPersonEmail EQUAL email] :: [RefinedFilter Person String]) []
  return $ do
    maybePerson <- maybePersonTagged
    return $ case maybePerson of
               [] -> error "aaaa" -- Can't occur
               (Entity uid person):_ -> (uid, person)

getFriendPrintout :: User -> Tagged (PersonId, Person) -> String
getFriendPrintout user taggedPerson =
  if isUserVerified user then
    let (_, Person _ name street number) = safeUnwrap taggedPerson user in
      name ++ (fromString ": ") ++ (fromString (show number)) ++ (fromString " ") ++ street
  else ""

getRequestPrintout :: User -> Tagged (PersonId, Person) -> (PersonId, String)
getRequestPrintout user taggedPerson =
  let (pid, Person _ name _ _) = if isUserVerified user
                                 then safeUnwrap taggedPerson user
                                 else error "cannot occur"
  in (pid, name)

getConfirmLinkR :: String -> Handler Html
getConfirmLinkR link = do
  defaultLayout $ do
    setTitle "Create Account"
    $(widgetFile "showlink")


{-@ unwrapDouble :: User<{\u -> isVerified u}> -> Tagged (Handler (Tagged (Handler a))) -> Handler a @-}
unwrapDouble :: User -> Tagged (Handler (Tagged (Handler a))) -> Handler a
unwrapDouble user xTHTH = do
  xTH <- safeUnwrap xTHTH user
  x <- safeUnwrap xTH user
  return x


getFriends :: (Tagged (Maybe (PersonId, Person))) -> User -> Handler [String]
getFriends _ _ = undefined
{- getFriends pidT user = do
  friendEmailListTHT <- return $ fmap (\pidOpt ->
                         case pidOpt of
                           Just (pid, _) -> Queries.getFriendList pid
                           Nothing -> return $ return [])
                         pidT

  friendPersonListTHTHL <- return $ fmap (fmap (fmap (\friendEmailList ->
                            mapM getPersonDetails $ map unpack friendEmailList)))
                            friendEmailListTHT

  friendListTHTHL <- return $ fmap (fmap (fmap (fmap (
                      map (getFriendPrintout user)))))
                      friendPersonListTHTHL

  friendList <- if isUserVerified user
                 then unwrapDouble user friendListTHTHL
                 else return []
  return friendList
-}

getRequests :: (Tagged (Maybe (PersonId, Person))) -> User -> Handler [(PersonId, String)]
getRequests _ _ = undefined
{- getRequests pidT user = do
  requestEmailListTHT <- return $ fmap (\pidOpt ->
                         case pidOpt of
                           Just (pid, _) -> Queries.getRequestList pid
                           Nothing -> return $ return [])
                         pidT

  requestPersonListTHTHL <- return $ fmap (fmap (fmap (\requestEmailList ->
                            mapM getPersonDetails $ map unpack requestEmailList)))
                            requestEmailListTHT

  requestListTHTHL <- return $ fmap (fmap (fmap (fmap (
                      map (getRequestPrintout user)))))
                      requestPersonListTHTHL

  requestList <- if isUserVerified user
                 then unwrapDouble user requestListTHTHL
                 else return []
  return requestList
-}

{-@ getLink :: (Tagged<{\u -> isVerified u}> (Maybe (PersonId, Person))) -> Maybe User -> Route App @-}
getLink :: Tagged (Maybe (PersonId, Person)) -> Maybe User -> Route App
getLink maybePersonTagged maybeUser =
    let linkT = BinahLibrary.liftM (\maybePerson ->
                         case maybePerson of
                           Nothing -> AuthR LoginR
                           Just (uid, _) -> ProfileR uid)
                maybePersonTagged
    in case maybeUser of
         Just user -> if isUserVerified user
                      then safeUnwrap linkT user
                      else AuthR LoginR
         Nothing -> AuthR LoginR


getHomeR :: Handler Html
getHomeR = do
    myId <- maybeAuthId
    maybePersonTagged <- Queries.getAuthPerson
    maybeUser <- Queries.getAuthUser
    loggedIn <- return $ case maybeUser of
                           Nothing -> False
                           Just user -> if isUserVerified user then
                                          case safeUnwrap maybePersonTagged user of
                                            Nothing -> False
                                            Just _ -> True
                                        else False

    link <- return $ getLink maybePersonTagged maybeUser
    requestList <- return ([] :: [(PersonId, String)])
    friendList <- return ([] :: [String])
    {-
    friendList <- case maybeUser of
                    Just user -> if isUserVerified user
                                 then getFriends maybePersonTagged user
                                 else return []
                    Nothing -> return []
    requestList <- case maybeUser of
                    Just user -> if isUserVerified user
                                 then getRequests maybePersonTagged user
                                 else return []
                    Nothing -> return []
    -}
    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Welcome To Yesod!"
        $(widgetFile "homepage")


{-@ getAuthPerson :: Handler (Tagged<{\u -> isVerified u}> (Maybe (Key Person, Person))) @-}
getAuthPerson :: Handler (Tagged (Maybe (Key Person, Person)))
getAuthPerson = do
  myId <- maybeAuthId
  authPerson <- case myId of
                  Nothing -> return $ return Nothing
                  Just id -> runDB $ do
                    userOpt <- get id
                    user <- return $ Maybe.fromJust userOpt
                    entityPersonTagged <- selectPerson ([filterPersonEmail EQUAL (userEmail user)] :: [RefinedFilter Person String]) []
                    return $ do
                      entityPerson <- entityPersonTagged
                      return $ case entityPerson of
                                 [] -> Nothing
                                 (Entity uid person):_ -> Just (uid, person)
  return authPerson
