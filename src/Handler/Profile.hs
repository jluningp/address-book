{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-}

module Handler.Profile where

import Yesod.Form.Jquery
import Import
import BinahLibrary hiding (filter)
import qualified Data.Maybe as Maybe

data PersonDetails = PersonDetails Text Text Int

personForm :: Person -> Html -> MForm Handler (FormResult PersonDetails, Widget)
personForm (Person email name street number)  = renderDivs $ PersonDetails
  <$> areq textField "Name:    " (Just $ pack name)
  <*> areq textField "Street:  " (Just $ pack street)
  <*> areq intField "Number:  " (Just $ number)


getProfileR :: PersonId -> Handler Html
getProfileR personId = do
{-  taggedPerson <- runDB $ do
    taggedPersonList <- selectPerson [filterPersonId EQUAL personId] []
    return $ do
      personList <- taggedPersonList
      return $ case personList of
                 [] -> error "No id found"
                 p:_ -> p
-}

  authUsr <- maybeAuthId
  user <- runDB $ get404 (Maybe.fromJust authUsr)
  Person email name street number <- runDB $ get404 personId --safeUnwrap taggedPerson user
  (widget, enctype) <- generateFormPost $ personForm (Person email name street number)
  canEditTagged <- BinahLibrary.isMe personId
  canEdit <- return $ safeUnwrap canEditTagged user
  defaultLayout $ do
    $(widgetFile "profile")

{-@ nonEmpty :: {l:[a] | True} -> {r:Bool | r <=> (len(l) > 0)} @-}
nonEmpty :: [a] -> Bool
nonEmpty [] = False
nonEmpty (x:xs) = True


postUpdatePersonR :: PersonId -> Handler ()
postUpdatePersonR personId = do
  Person email name street number <- runDB $ get404 personId
  ((result, widget), enctype) <- runFormPost $ personForm (Person email name street number)
  case result of
    FormSuccess (PersonDetails name street number) ->
      let uname = unpack name
          ustreet = unpack street
      in
      if nonEmpty uname && nonEmpty ustreet && number > 0
      then runDB $ do
        refinedUpdate personId [PersonName =# uname]
        refinedUpdate personId [PersonStreet =# ustreet]
        refinedUpdate personId [PersonNumber =# number]
      else liftIO $ print "Invalid Input"
    _ -> liftIO $ print "An Odd Error Occurred"
  redirect $ ProfileR personId
