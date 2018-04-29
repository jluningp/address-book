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
import           TaggedUser
import           TaggedEmail
import           TaggedPerson
import           TaggedFriends

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

{-@ getPersonDetails :: String -> Handler (TaggedPerson<{\u -> isVerified u}> (PersonId, Person)) @-}
getPersonDetails :: String -> Handler (TaggedPerson (PersonId, Person))
getPersonDetails email = do
  maybePersonTagged <- runDB $ selectPerson ([filterPersonEmail EQUAL email] :: [RefinedFilter Person String]) []
  return $ do
    maybePerson <- maybePersonTagged
    return $ case maybePerson of
               [] -> error "aaaa" -- Can't occur
               (Entity uid person):_ -> (uid, person)

getFriendPrintout :: User -> TaggedPerson (PersonId, Person) -> String
getFriendPrintout user taggedPerson =
  if isUserVerified user then
    let taggedRow = TaggedPerson.liftM snd taggedPerson in
    let (_, Person _ name street number) = safeUnwrapPerson taggedRow (return user) taggedPerson in
      name ++ (fromString ": ") ++ (fromString (show number)) ++ (fromString " ") ++ street
  else ""

getRequestPrintout :: User -> TaggedPerson (PersonId, Person) -> (PersonId, String)
getRequestPrintout user taggedPerson =
  let (pid, Person _ name _ _) = if isUserVerified user
                                 then let taggedRow = TaggedPerson.liftM snd taggedPerson
                                      in safeUnwrapPerson taggedRow (return user) taggedPerson
                                 else error "cannot occur"
  in (pid, name)

getConfirmLinkR :: String -> Handler Html
getConfirmLinkR link = do
  defaultLayout $ do
    setTitle "Create Account"
    $(widgetFile "showlink")


{-@ unwrapDouble :: TaggedPerson Person -> TaggedFriends Friends -> User<{\u -> isVerified u}> -> TaggedPerson (Handler (TaggedFriends (Handler a))) -> Handler a @-}
unwrapDouble :: TaggedPerson Person -> TaggedFriends Friends -> User -> TaggedFriends (Handler (TaggedPerson (Handler a))) -> Handler a
unwrapDouble rowP rowF user xTHTH = do
  xTH <- safeUnwrapPerson rowP (return user) xTHTH
  x <- safeUnwrapPerson rowF (return user) xTH
  return x


getFriends :: (TaggedPerson (Maybe (PersonId, Person))) -> User -> Handler [String]
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

getRequests :: (TaggedPerson (Maybe (PersonId, Person))) -> User -> Handler [(PersonId, String)]
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

{-@ getLink :: (TaggedPerson<{\u -> isVerified u}> (Maybe (PersonId, Person))) -> Maybe User -> Route App @-}
getLink :: TaggedPerson (Maybe (PersonId, Person)) -> Maybe User -> Route App
getLink maybePersonTagged maybeUser =
    let linkT = TaggedPerson.liftM (\maybePerson ->
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
    friendList <- case maybeUser of
                    Just user -> if isUserVerified user
                                 then getFriends maybePersonTagged user
                                 else return []
                    Nothing -> return []
    {- requestList <- case maybeUser of
                    Just user -> if isUserVerified user
                                 then getRequests maybePersonTagged user
                                 else return []
                    Nothing -> return []
    -}
    defaultLayout $ do
        aDomId <- newIdent
        setTitle "Welcome To Yesod!"
        $(widgetFile "homepage")


{-@ getAuthPerson :: Handler (TaggedPerson<{\u -> isVerified u}> (Maybe (Key Person, Person))) @-}
getAuthPerson :: Handler (TaggedPerson (Maybe (Key Person, Person)))
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
