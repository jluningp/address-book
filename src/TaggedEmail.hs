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

module TaggedEmail where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Model
import           Data.Text hiding (map, filter)

{-@ data TaggedEmail a <p :: Email -> User -> Bool> = TaggedEmail { emailContent :: a } @-}
data TaggedEmail a = TaggedEmail { emailContent :: a }
{-@ data variance TaggedEmail covariant contravariant @-}

instance Functor TaggedEmail where
    fmap f (TaggedEmail x) = TaggedEmail (f x)

instance Applicative TaggedEmail where
  pure  = TaggedEmail
  (TaggedEmail f) <*> (TaggedEmail x) = TaggedEmail (f x)

instance Monad TaggedEmail where
    return x = TaggedEmail x
    (TaggedEmail x) >>= f = f x
    (TaggedEmail _) >>  t = t
    fail          = error

{-@ instance Monad TaggedEmail where
     >>= :: forall <p :: Email -> User -> Bool, f:: a -> b -> Bool>.
            x:TaggedEmail <p> a
         -> (u:a -> TaggedEmail <p> (b <f u>))
         -> TaggedEmail <p> (b<f (emailContent x)>);
     >>  :: x:TaggedEmail a
         -> TaggedEmail b
         -> TaggedEmail b;
     return :: forall <p :: Email -> User -> Bool>. a -> TaggedEmail <p> a
@-}
