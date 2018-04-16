{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-@ LIQUID "--no-adt"                   @-}
{-@ LIQUID "--exact-data-con"           @-}
{-@ LIQUID "--higherorder"              @-}
{-@ LIQUID "--no-termination"           @-}

module Model where

import Prelude
import ClassyPrelude.Yesod
import Database.Persist.Quasi

{-@
data User = User
	{ userEmail :: [Char]
	, userPassword :: Maybe [Char]
	, userVerkey :: Maybe [Char]
	, userVerified :: Bool
	}
@-}

{-@
data EntityField User typ where
   Model.UserEmail :: EntityField User {v:_ | True}
 | Model.UserPassword :: EntityField User {v:_ | True}
 | Model.UserVerkey :: EntityField User {v:_ | True}
 | Model.UserVerified :: EntityField User {v:_ | True}
 | Model.UserId :: EntityField User {v:_ | True}
@-}

{-@
data Email = Email
	{ emailEmail :: [Char]
	, emailUserId :: Maybe UserId
	, emailVerkey :: Maybe [Char]
	}
@-}

{-@
data EntityField Email typ where
   Model.EmailEmail :: EntityField Email {v:_ | True}
 | Model.EmailUserId :: EntityField Email {v:_ | True}
 | Model.EmailVerkey :: EntityField Email {v:_ | True}
 | Model.EmailId :: EntityField Email {v:_ | True}
@-}

{-@
data Person = Person
	{ personEmail :: [Char]
	, personName :: {n:[Char] | len n > 0}
	, personStreet :: {n:[Char] | len n > 0}
	, personNumber :: {v:Int | v > 0}
	}
@-}

{-@
data EntityField Person typ where
   Model.PersonEmail :: EntityField Person {v:_ | True}
 | Model.PersonName :: EntityField Person {n:_ | len n > 0}
 | Model.PersonStreet :: EntityField Person {n:_ | len n > 0}
 | Model.PersonNumber :: EntityField Person {v:_ | v > 0}
 | Model.PersonId :: EntityField Person {v:_ | True}
@-}

{-@
data Friends = Friends
	{ friendsEmail :: [Char]
	, friendsRequests :: [[Char]]
	, friendsFriends :: [[Char]]
	, friendsOutgoingRequests :: [[Char]]
	}
@-}

{-@
data EntityField Friends typ where
   Model.FriendsEmail :: EntityField Friends {v:_ | True}
 | Model.FriendsRequests :: EntityField Friends {v:_ | True}
 | Model.FriendsFriends :: EntityField Friends {v:_ | True}
 | Model.FriendsOutgoingRequests :: EntityField Friends {v:_ | True}
 | Model.FriendsId :: EntityField Friends {v:_ | True}
@-}

-- You can define all of your database entities in the entities file.
-- You can find more information on persistent and how to declare entities
-- at:
-- http://www.yesodweb.com/book/persistent/
share [mkPersist sqlSettings, mkMigrate "migrateAll"]
  $(persistFileWith lowerCaseSettings "config/models")
