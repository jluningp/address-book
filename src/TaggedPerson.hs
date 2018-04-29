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

module TaggedPerson where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Model
import           Data.Text hiding (map, filter)

{-@ data TaggedPerson a <p :: Person -> User -> Bool> = TaggedPerson { personContent :: a } @-}
data TaggedPerson a = TaggedPerson { personContent :: a }
{-@ data variance TaggedPerson covariant contravariant @-}

instance Functor TaggedPerson where
    fmap f (TaggedPerson x) = TaggedPerson (f x)

instance Applicative TaggedPerson where
  pure  = TaggedPerson
  (TaggedPerson f) <*> (TaggedPerson x) = TaggedPerson (f x)

instance Monad TaggedPerson where
    return x = TaggedPerson x
    (TaggedPerson x) >>= f = f x
    (TaggedPerson _) >>  t = t
    fail          = error

{-@ instance Monad TaggedPerson where
     >>= :: forall <p :: Person -> User -> Bool, f:: a -> b -> Bool>.
            x:TaggedPerson <p> a
         -> (u:a -> TaggedPerson <p> (b <f u>))
         -> TaggedPerson <p> (b<f (personContent x)>);
     >>  :: x:TaggedPerson a
         -> TaggedPerson b
         -> TaggedPerson b;
     return :: forall <p :: Person -> User -> Bool>. a -> TaggedPerson <p> a
@-}
