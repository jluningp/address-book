import Language.Haskell.Liquid.Prelude

{-@
data User = 
	{ userEmail :: Text
	, userPassword :: Text Maybe
	, userVerkey :: Text Maybe
	, userVerified :: Bool
	, userUniqueUser :: email
	}
@-}

{-@
data EntityField User typ where 
   UserEmail :: EntityField User Text
 | UserPassword :: EntityField User Text Maybe
 | UserVerkey :: EntityField User Text Maybe
 | UserVerified :: EntityField User Bool
 | UserUniqueUser :: EntityField User email
@-}

{-@
data Email = 
	{ emailEmail :: Text
	, emailUserId :: UserId Maybe
	, emailVerkey :: Text Maybe
	, emailUniqueEmail :: email
	, emailComment :: json
	, emailMessage :: Text
	, emailUserId :: UserId Maybe
	}
@-}

{-@
data EntityField Email typ where 
   EmailEmail :: EntityField Email Text
 | EmailUserId :: EntityField Email UserId Maybe
 | EmailVerkey :: EntityField Email Text Maybe
 | EmailUniqueEmail :: EntityField Email email
 | EmailComment :: EntityField Email json
 | EmailMessage :: EntityField Email Text
 | EmailUserId :: EntityField Email UserId Maybe
@-}

{-@
data Person = 
	{ personEmail :: Text
	, personUniquePerson :: email
	, personName :: Text
	, personStreet :: Text
	, personNumber :: {x:Int | x >= 0}
	}
@-}

{-@
data EntityField Person typ where 
   PersonEmail :: EntityField Person Text
 | PersonUniquePerson :: EntityField Person email
 | PersonName :: EntityField Person Text
 | PersonStreet :: EntityField Person Text
 | PersonNumber :: EntityField Person {x:Int | x >= 0}
@-}

{-@
data Friends = 
	{ friendsEmail :: Text
	, friendsUniqueFriend :: email
	, friendsRequests :: [Text]
	, friendsFriends :: [Text]
	, friendsOutgoingRequests :: [Text]
	}
@-}

{-@
data EntityField Friends typ where 
   FriendsEmail :: EntityField Friends Text
 | FriendsUniqueFriend :: EntityField Friends email
 | FriendsRequests :: EntityField Friends [Text]
 | FriendsFriends :: EntityField Friends [Text]
 | FriendsOutgoingRequests :: EntityField Friends [Text]
@-}
