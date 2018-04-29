{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--exact-data-con"                      @-}

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

--{-@ assume Prelude.error :: String -> a @-}

{-@ getPersonDetails :: String -> Handler (Tagged<{\u -> isVerified u}> (PersonId, Person)) @-}
getPersonDetails :: String -> Handler (Tagged (PersonId, Person))
getPersonDetails email = do
  maybePersonTagged <- runDB $ selectPerson ([{-filterPersonEmail EQUAL "foo"-}] :: [RefinedFilter Person String]) []
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


getHomeR :: Handler Html
getHomeR = do
    myId <- maybeAuthId
    maybePersonTagged <- Handler.Home.getAuthPerson
    maybeUser <- Queries.getAuthUser
    loggedIn <- return $ case maybeUser of
                           Nothing -> False
                           Just user -> if isUserVerified user then
                                          case safeUnwrap maybePersonTagged user of
                                            Nothing -> False
                                            Just _ -> True
                                        else False
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
                 Just (pid, _) -> Handler.Home.getFriendList pid
                 Nothing -> return $ return []
    requestEmailListTaggedHandlerTagged <- return $ do
      maybePerson <- maybePersonTagged
      return $ case maybePerson of
                 Just (pid, _) -> Handler.Home.getRequestList pid
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
                              Just user -> if isUserVerified user
                                           then map (getRequestPrintout user) l
                                           else []) hl) thl) hthl) requestPersonList
    friendListH <- case maybeUser of
                       Nothing -> return $ return []
                       Just user -> if isUserVerified user
                                    then return $ do
                         friendListTHL <- safeUnwrap friendListTHTHL user
                         friendList <- safeUnwrap friendListTHL user
                         return friendList
                                    else return $ return []
    friendList <- friendListH

    requestListH <- case maybeUser of
                       Nothing -> return $ return []
                       Just user -> if isUserVerified user
                                    then return $ do
                         requestListTHL <- safeUnwrap requestListTHTHL user
                         requestList <- safeUnwrap requestListTHL user
                         return requestList
                                    else return $ return []
    requestList <- requestListH

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
                    entityPersonTagged <- selectPerson ([{-filterPersonEmail EQUAL (userEmail user)-}] :: [RefinedFilter Person String]) []
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
getFriendList = Handler.Home.getList friendsFriends
{-@ getRequestList :: PersonId -> Handler (Tagged<{\u -> isVerified u}> [Text]) @-}
getRequestList = Handler.Home.getList friendsRequests
{-@ getOutgoingRequestList :: PersonId -> Handler (Tagged<{\u -> isVerified u}> [Text]) @-}
getOutgoingRequestList = Handler.Home.getList friendsOutgoingRequests
