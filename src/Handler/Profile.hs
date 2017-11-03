{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Profile where

import Import

getProfileR :: PersonId -> Handler Html
getProfileR personId = do
  Person email name street number <- runDB $ get404 personId
  defaultLayout $ do
    $(widgetFile "profile")
