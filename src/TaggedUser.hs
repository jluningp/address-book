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

module TaggedUser where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Model
import           Data.Text hiding (map, filter)

{-@ data TaggedUser a <p :: User -> User -> Bool> = TaggedUser { userContent :: a } @-}
data TaggedUser a = TaggedUser { userContent :: a }
{-@ data variance TaggedUser covariant contravariant @-}

instance Functor TaggedUser where
    fmap f (TaggedUser x) = TaggedUser (f x)

instance Applicative TaggedUser where
  pure  = TaggedUser
  (TaggedUser f) <*> (TaggedUser x) = TaggedUser (f x)

instance Monad TaggedUser where
    return x = TaggedUser x
    (TaggedUser x) >>= f = f x
    (TaggedUser _) >>  t = t
    fail          = error

{-@ instance Monad TaggedUser where
     >>= :: forall <p :: User -> User -> Bool, f:: a -> b -> Bool>.
            x:TaggedUser <p> a
         -> (u:a -> TaggedUser <p> (b <f u>))
         -> TaggedUser <p> (b<f (userContent x)>);
     >>  :: x:TaggedUser a
         -> TaggedUser b
         -> TaggedUser b;
     return :: forall <p :: User -> User -> Bool>. a -> TaggedUser <p> a
@-}
