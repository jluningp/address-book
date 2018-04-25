
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-}

module BinahLibrary where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Model
import           Data.Text hiding (map, filter)

{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }
{-@ data variance Tagged covariant contravariant @-}

data RefinedPersistFilter = EQUAL | NE | LE | LTP | GE | GTP

{-@ data RefinedFilter record typ <p :: User -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }
  @-}
{-@ data variance RefinedFilter covariant covariant contravariant @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }


{-@ data RefinedUpdate record typ = RefinedUpdate
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ } @-}
data RefinedUpdate record typ = RefinedUpdate
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ
    }

(=#) :: EntityField v typ -> typ -> RefinedUpdate v typ
x =# y = RefinedUpdate x y

{-@ reflect ==# @-}
(==#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field ==# value = RefinedFilter field value EQUAL

{-@ reflect /=# @-}
(/=#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field /=# value = RefinedFilter field value NE

{-@ reflect <=# @-}
(<=#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field <=# value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = LE
  }

{-@ reflect <# @-}
(<#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field <# value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = LTP
  }

{-@ reflect >=# @-}
(>=#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field >=# value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = GE
  }

{-@ reflect ># @-}
(>#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field ># value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = GE
  }


toPersistentFilter :: PersistField typ =>
                      RefinedFilter record typ -> Filter record
toPersistentFilter filter =
    case refinedFilterFilter filter of
         EQUAL -> (refinedFilterField filter) ==. (refinedFilterValue filter)
         NE -> (refinedFilterField filter) !=. (refinedFilterValue filter)
         LE -> (refinedFilterField filter) <=. (refinedFilterValue filter)
         LTP -> (refinedFilterField filter) <. (refinedFilterValue filter)
         GE -> (refinedFilterField filter) >=. (refinedFilterValue filter)
         GTP -> (refinedFilterField filter) >. (refinedFilterValue filter)

toPersistentUpdate :: PersistField typ =>
                      RefinedUpdate record typ -> Update record
toPersistentUpdate (RefinedUpdate a b) = a =. b

refinedUpdate id us = update id (map toPersistentUpdate us)

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQUserEmail @-}
evalQUserEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail EQUAL filter given = given == filter
evalQUserEmail LE filter given = given <= filter
evalQUserEmail GE filter given = given >= filter
evalQUserEmail LTP filter given = given < filter
evalQUserEmail GTP filter given = given > filter
evalQUserEmail NE filter given = given /= filter

{-@ reflect evalQUserPassword @-}
evalQUserPassword :: RefinedPersistFilter -> Maybe [Char] -> Maybe [Char] -> Bool
evalQUserPassword EQUAL filter given = given == filter
evalQUserPassword NE filter given = given /= filter

{-@ reflect evalQUserVerkey @-}
evalQUserVerkey :: RefinedPersistFilter -> Maybe [Char] -> Maybe [Char] -> Bool
evalQUserVerkey EQUAL filter given = given == filter
evalQUserVerkey NE filter given = given /= filter

{-@ reflect evalQUserVerified @-}
evalQUserVerified :: RefinedPersistFilter -> Bool -> Bool -> Bool
evalQUserVerified EQUAL filter given = given == filter
evalQUserVerified NE filter given = given /= filter

{-@ reflect evalQUser @-}
evalQUser :: RefinedFilter User typ -> User -> Bool
evalQUser filter x = case refinedFilterField filter of
    UserEmail -> evalQUserEmail (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail x)
    UserPassword -> evalQUserPassword (refinedFilterFilter filter) (refinedFilterValue filter) (userPassword x)
    UserVerkey -> evalQUserVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (userVerkey x)
    UserVerified -> evalQUserVerified (refinedFilterFilter filter) (refinedFilterValue filter) (userVerified x)
    UserId -> False

{-@ reflect evalQsUser @-}
evalQsUser :: [RefinedFilter User typ] -> User -> Bool
evalQsUser (f:fs) x = evalQUser f x && (evalQsUser fs x)
evalQsUser [] _ = True

{-@ reflect evalQEmailEmail @-}
evalQEmailEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQEmailEmail EQUAL filter given = given == filter
evalQEmailEmail LE filter given = given <= filter
evalQEmailEmail GE filter given = given >= filter
evalQEmailEmail LTP filter given = given < filter
evalQEmailEmail GTP filter given = given > filter
evalQEmailEmail NE filter given = given /= filter

{-@ reflect evalQEmailUserId @-}
evalQEmailUserId :: RefinedPersistFilter -> Maybe UserId -> Maybe UserId -> Bool
evalQEmailUserId EQUAL filter given = given == filter
evalQEmailUserId NE filter given = given /= filter

{-@ reflect evalQEmailVerkey @-}
evalQEmailVerkey :: RefinedPersistFilter -> Maybe [Char] -> Maybe [Char] -> Bool
evalQEmailVerkey EQUAL filter given = given == filter
evalQEmailVerkey NE filter given = given /= filter

{-@ reflect evalQEmail @-}
evalQEmail :: RefinedFilter Email typ -> Email -> Bool
evalQEmail filter x = case refinedFilterField filter of
    EmailEmail -> evalQEmailEmail (refinedFilterFilter filter) (refinedFilterValue filter) (emailEmail x)
    EmailUserId -> evalQEmailUserId (refinedFilterFilter filter) (refinedFilterValue filter) (emailUserId x)
    EmailVerkey -> evalQEmailVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (emailVerkey x)
    EmailId -> False

{-@ reflect evalQsEmail @-}
evalQsEmail :: [RefinedFilter Email typ] -> Email -> Bool
evalQsEmail (f:fs) x = evalQEmail f x && (evalQsEmail fs x)
evalQsEmail [] _ = True

{-@ reflect evalQPersonEmail @-}
evalQPersonEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQPersonEmail EQUAL filter given = given == filter
evalQPersonEmail LE filter given = given <= filter
evalQPersonEmail GE filter given = given >= filter
evalQPersonEmail LTP filter given = given < filter
evalQPersonEmail GTP filter given = given > filter
evalQPersonEmail NE filter given = given /= filter

{-@ reflect evalQPersonName @-}
evalQPersonName :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQPersonName EQUAL filter given = given == filter
evalQPersonName LE filter given = given <= filter
evalQPersonName GE filter given = given >= filter
evalQPersonName LTP filter given = given < filter
evalQPersonName GTP filter given = given > filter
evalQPersonName NE filter given = given /= filter

{-@ reflect evalQPersonStreet @-}
evalQPersonStreet :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQPersonStreet EQUAL filter given = given == filter
evalQPersonStreet LE filter given = given <= filter
evalQPersonStreet GE filter given = given >= filter
evalQPersonStreet LTP filter given = given < filter
evalQPersonStreet GTP filter given = given > filter
evalQPersonStreet NE filter given = given /= filter

{-@ reflect evalQPersonNumber @-}
evalQPersonNumber :: RefinedPersistFilter -> Int -> Int -> Bool
evalQPersonNumber EQUAL filter given = given == filter
evalQPersonNumber LE filter given = given <= filter
evalQPersonNumber GE filter given = given >= filter
evalQPersonNumber LTP filter given = given < filter
evalQPersonNumber GTP filter given = given > filter
evalQPersonNumber NE filter given = given /= filter

{-@ reflect evalQPerson @-}
evalQPerson :: RefinedFilter Person typ -> Person -> Bool
evalQPerson filter x = case refinedFilterField filter of
    PersonEmail -> evalQPersonEmail (refinedFilterFilter filter) (refinedFilterValue filter) (personEmail x)
    PersonName -> evalQPersonName (refinedFilterFilter filter) (refinedFilterValue filter) (personName x)
    PersonStreet -> evalQPersonStreet (refinedFilterFilter filter) (refinedFilterValue filter) (personStreet x)
    PersonNumber -> evalQPersonNumber (refinedFilterFilter filter) (refinedFilterValue filter) (personNumber x)
    PersonId -> False

{-@ reflect evalQsPerson @-}
evalQsPerson :: [RefinedFilter Person typ] -> Person -> Bool
evalQsPerson (f:fs) x = evalQPerson f x && (evalQsPerson fs x)
evalQsPerson [] _ = True

{-@ reflect evalQFriendsEmail @-}
evalQFriendsEmail :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQFriendsEmail EQUAL filter given = given == filter
evalQFriendsEmail LE filter given = given <= filter
evalQFriendsEmail GE filter given = given >= filter
evalQFriendsEmail LTP filter given = given < filter
evalQFriendsEmail GTP filter given = given > filter
evalQFriendsEmail NE filter given = given /= filter

{-@ reflect evalQFriendsRequests @-}
evalQFriendsRequests :: RefinedPersistFilter -> [[Char]] -> [[Char]] -> Bool
evalQFriendsRequests EQUAL filter given = given == filter
evalQFriendsRequests LE filter given = given <= filter
evalQFriendsRequests GE filter given = given >= filter
evalQFriendsRequests LTP filter given = given < filter
evalQFriendsRequests GTP filter given = given > filter
evalQFriendsRequests NE filter given = given /= filter

{-@ reflect evalQFriendsFriends @-}
evalQFriendsFriends :: RefinedPersistFilter -> [[Char]] -> [[Char]] -> Bool
evalQFriendsFriends EQUAL filter given = given == filter
evalQFriendsFriends LE filter given = given <= filter
evalQFriendsFriends GE filter given = given >= filter
evalQFriendsFriends LTP filter given = given < filter
evalQFriendsFriends GTP filter given = given > filter
evalQFriendsFriends NE filter given = given /= filter

{-@ reflect evalQFriendsOutgoingRequests @-}
evalQFriendsOutgoingRequests :: RefinedPersistFilter -> [[Char]] -> [[Char]] -> Bool
evalQFriendsOutgoingRequests EQUAL filter given = given == filter
evalQFriendsOutgoingRequests LE filter given = given <= filter
evalQFriendsOutgoingRequests GE filter given = given >= filter
evalQFriendsOutgoingRequests LTP filter given = given < filter
evalQFriendsOutgoingRequests GTP filter given = given > filter
evalQFriendsOutgoingRequests NE filter given = given /= filter

{-@ reflect evalQFriends @-}
evalQFriends :: RefinedFilter Friends typ -> Friends -> Bool
evalQFriends filter x = case refinedFilterField filter of
    FriendsEmail -> evalQFriendsEmail (refinedFilterFilter filter) (refinedFilterValue filter) (friendsEmail x)
    FriendsRequests -> evalQFriendsRequests (refinedFilterFilter filter) (refinedFilterValue filter) (friendsRequests x)
    FriendsFriends -> evalQFriendsFriends (refinedFilterFilter filter) (refinedFilterValue filter) (friendsFriends x)
    FriendsOutgoingRequests -> evalQFriendsOutgoingRequests (refinedFilterFilter filter) (refinedFilterValue filter) (friendsOutgoingRequests x)
    FriendsId -> False

{-@ reflect evalQsFriends @-}
evalQsFriends :: [RefinedFilter Friends typ] -> Friends -> Bool
evalQsFriends (f:fs) x = evalQFriends f x && (evalQsFriends fs x)
evalQsFriends [] _ = True

{-@ filterUserEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u -> true}> User (String) @-}
{-@ reflect filterUserEmail @-}
filterUserEmail :: RefinedPersistFilter -> String -> RefinedFilter User (String)
filterUserEmail f v = RefinedFilter UserEmail v f

{-@ filterUserPassword :: RefinedPersistFilter -> Maybe String -> RefinedFilter<{\u -> true}> User (Maybe String) @-}
{-@ reflect filterUserPassword @-}
filterUserPassword :: RefinedPersistFilter -> Maybe String -> RefinedFilter User (Maybe String)
filterUserPassword f v = RefinedFilter UserPassword v f

{-@ filterUserVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter<{\u -> true}> User (Maybe String) @-}
{-@ reflect filterUserVerkey @-}
filterUserVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter User (Maybe String)
filterUserVerkey f v = RefinedFilter UserVerkey v f

{-@ filterUserVerified :: RefinedPersistFilter -> Bool -> RefinedFilter<{\u -> true}> User (Bool) @-}
{-@ reflect filterUserVerified @-}
filterUserVerified :: RefinedPersistFilter -> Bool -> RefinedFilter User (Bool)
filterUserVerified f v = RefinedFilter UserVerified v f

{-@ filterEmailEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u -> true}> Email (String) @-}
{-@ reflect filterEmailEmail @-}
filterEmailEmail :: RefinedPersistFilter -> String -> RefinedFilter Email (String)
filterEmailEmail f v = RefinedFilter EmailEmail v f

{-@ filterEmailUserId :: RefinedPersistFilter -> Maybe UserId -> RefinedFilter<{\u -> true}> Email (Maybe UserId) @-}
{-@ reflect filterEmailUserId @-}
filterEmailUserId :: RefinedPersistFilter -> Maybe UserId -> RefinedFilter Email (Maybe UserId)
filterEmailUserId f v = RefinedFilter EmailUserId v f

{-@ filterEmailVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter<{\u -> true}> Email (Maybe String) @-}
{-@ reflect filterEmailVerkey @-}
filterEmailVerkey :: RefinedPersistFilter -> Maybe String -> RefinedFilter Email (Maybe String)
filterEmailVerkey f v = RefinedFilter EmailVerkey v f

{-@ filterPersonEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u -> true}> Person (String) @-}
{-@ reflect filterPersonEmail @-}
filterPersonEmail :: RefinedPersistFilter -> String -> RefinedFilter Person (String)
filterPersonEmail f v = RefinedFilter PersonEmail v f

{-@ filterPersonName :: RefinedPersistFilter -> {n:String | len n > 0} -> RefinedFilter<{\u -> true}> Person (String) @-}
{-@ reflect filterPersonName @-}
filterPersonName :: RefinedPersistFilter -> String -> RefinedFilter Person (String)
filterPersonName f v = RefinedFilter PersonName v f

{-@ filterPersonStreet :: RefinedPersistFilter -> {n:String | len n > 0} -> RefinedFilter<{\u -> true}> Person (String) @-}
{-@ reflect filterPersonStreet @-}
filterPersonStreet :: RefinedPersistFilter -> String -> RefinedFilter Person (String)
filterPersonStreet f v = RefinedFilter PersonStreet v f

{-@ filterPersonNumber :: RefinedPersistFilter -> {v:Int | v > 0} -> RefinedFilter<{\u -> userEmail u == "test@gmail.com"}> Person (Int) @-}
{-@ reflect filterPersonNumber @-}
filterPersonNumber :: RefinedPersistFilter -> Int -> RefinedFilter Person (Int)
filterPersonNumber f v = RefinedFilter PersonNumber v f

{-@ filterFriendsEmail :: RefinedPersistFilter -> String -> RefinedFilter<{\u -> true}> Friends (String) @-}
{-@ reflect filterFriendsEmail @-}
filterFriendsEmail :: RefinedPersistFilter -> String -> RefinedFilter Friends (String)
filterFriendsEmail f v = RefinedFilter FriendsEmail v f

{-@ filterFriendsRequests :: RefinedPersistFilter -> [String] -> RefinedFilter<{\u -> true}> Friends ([String]) @-}
{-@ reflect filterFriendsRequests @-}
filterFriendsRequests :: RefinedPersistFilter -> [String] -> RefinedFilter Friends ([String])
filterFriendsRequests f v = RefinedFilter FriendsRequests v f

{-@ filterFriendsFriends :: RefinedPersistFilter -> [String] -> RefinedFilter<{\u -> true}> Friends ([String]) @-}
{-@ reflect filterFriendsFriends @-}
filterFriendsFriends :: RefinedPersistFilter -> [String] -> RefinedFilter Friends ([String])
filterFriendsFriends f v = RefinedFilter FriendsFriends v f

{-@ filterFriendsOutgoingRequests :: RefinedPersistFilter -> [String] -> RefinedFilter<{\u -> true}> Friends ([String]) @-}
{-@ reflect filterFriendsOutgoingRequests @-}
filterFriendsOutgoingRequests :: RefinedPersistFilter -> [String] -> RefinedFilter Friends ([String])
filterFriendsOutgoingRequests f v = RefinedFilter FriendsOutgoingRequests v f

{-@ assume selectFriends :: forall <p:: User -> Bool>. f:[RefinedFilter<p> Friends typ]
                -> [SelectOpt Friends]
                -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged<p> [Entity {v:Friends | evalQsFriends f v}]) @-}
selectFriends :: (PersistEntityBackend Friends ~ BaseBackend backend,
      PersistEntity Friends, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Friends typ]
      -> [SelectOpt Friends]
      -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged [Entity Friends])
selectFriends fs ts = selectList (map toPersistentFilter fs) ts >>= return . Tagged

{-@ assume selectPerson :: forall <p:: User -> Bool>. f:[RefinedFilter<p> Person typ]
                -> [SelectOpt Person]
                -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged<p> [Entity {v:Person | evalQsPerson f v}]) @-}
selectPerson :: (PersistEntityBackend Person ~ BaseBackend backend,
      PersistEntity Person, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Person typ]
      -> [SelectOpt Person]
      -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged [Entity Person])
selectPerson fs ts = selectList (map toPersistentFilter fs) ts >>= return . Tagged

{-@ assume selectEmail :: forall <p:: User -> Bool>. f:[RefinedFilter<p> Email typ]
                -> [SelectOpt Email]
                -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged<p> [Entity {v:Email | evalQsEmail f v}]) @-}
selectEmail :: (PersistEntityBackend Email ~ BaseBackend backend,
      PersistEntity Email, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Email typ]
      -> [SelectOpt Email]
      -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged [Entity Email])
selectEmail fs ts = selectList (map toPersistentFilter fs) ts >>= return . Tagged

{-@ assume selectUser :: forall <p:: User -> Bool>. f:[RefinedFilter<p> User typ]
                -> [SelectOpt User]
                -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged<p> [Entity {v:User | evalQsUser f v}]) @-}
selectUser :: (PersistEntityBackend User ~ BaseBackend backend,
      PersistEntity User, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter User typ]
      -> [SelectOpt User]
      -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged [Entity User])
selectUser fs ts = selectList (map toPersistentFilter fs) ts >>= return . Tagged

{-@ safeShow :: forall <p :: User -> Bool>.
                Tagged<p> a
             -> User<p>
             -> String
@-}
safeShow :: Show a => Tagged a -> User -> String
safeShow (Tagged x) _ = show x

testSafeShow () = do
  taggedUsers <- selectPerson [filterPersonNumber EQUAL 3] []
  return $ safeShow taggedUsers (User "test@gmail.com" Nothing Nothing False)
