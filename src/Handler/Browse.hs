{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Handler.Browse where

import Import

getBrowseR :: Handler Html
getBrowseR = do
  people <- runDB $ selectList [] [Asc PersonName]
  defaultLayout $(widgetFile "browse")
