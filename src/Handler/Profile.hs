{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Profile where

import Yesod.Form.Jquery
import Import

data PersonDetails = PersonDetails Text Text Text

personForm :: Person -> Html -> MForm Handler (FormResult PersonDetails, Widget)
personForm (Person email name street number)  = renderDivs $ PersonDetails 
  <$> areq textField "Name:    " (Just name)
  <*> areq textField "Street:  " (Just street)
  <*> areq textField "Number:  " (Just number)
  

getProfileR :: PersonId -> Handler Html
getProfileR personId = do
  Person email name street number <- runDB $ get404 personId
  (widget, enctype) <- generateFormPost $ personForm (Person email name street number)
  canEdit <- Import.isMe personId
  defaultLayout $ do
    $(widgetFile "profile")

postUpdatePersonR :: PersonId -> Handler ()
postUpdatePersonR personId = do
  Person email name street number <- runDB $ get404 personId
  ((result, widget), enctype) <- runFormPost $ personForm (Person email name street number)
  case result of
    FormSuccess (PersonDetails name street number) -> runDB $ do
      update personId [PersonName =. name]
      update personId [PersonStreet =. street]
      update personId [PersonNumber =. number]
    _ -> liftIO $ print "wtf"
  redirect $ ProfileR personId
