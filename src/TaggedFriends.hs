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
{-@ LIQUID "--no-totality"                         @-}

module TaggedFriends where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Model
import           Data.Text hiding (map, filter)

{-@ data TaggedFriends a <p :: Friends -> User -> Bool> = TaggedFriends { friendsContent :: a } @-}
data TaggedFriends a = TaggedFriends { friendsContent :: a }
{-@ data variance TaggedFriends covariant contravariant @-}

instance Functor TaggedFriends where
    fmap f (TaggedFriends x) = TaggedFriends (f x)

instance Applicative TaggedFriends where
  pure  = TaggedFriends
  (TaggedFriends f) <*> (TaggedFriends x) = TaggedFriends (f x)

instance Monad TaggedFriends where
    return x = TaggedFriends x
    (TaggedFriends x) >>= f = f x
    (TaggedFriends _) >>  t = t
    fail          = error

{-@ instance Monad TaggedFriends where
     >>= :: forall <p :: Friends -> User -> Bool, f:: a -> b -> Bool>.
            x:TaggedFriends <p> a
         -> (u:a -> TaggedFriends <p> (b <f u>))
         -> TaggedFriends <p> (b<f (friendsContent x)>);
     >>  :: x:TaggedFriends a
         -> TaggedFriends b
         -> TaggedFriends b;
     return :: forall <p :: Friends -> User -> Bool>. a -> TaggedFriends <p> a
@-}


