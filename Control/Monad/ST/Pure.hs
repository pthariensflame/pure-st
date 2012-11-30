{-# LANGUAGE Rank2Types, MultiParamTypeClasses, DeriveDataTypeable, ScopedTypeVariables, FlexibleInstances, UndecidableInstances, Trustworthy, NoImplicitPrelude #-}
module Control.Monad.ST.Pure (ST,
                              runST,
                              fixST,
                              STT,
                              runSTT,
                              fixSTT,
                              STRef,
                              newSTRef,
                              modifySTRef,
                              writeSTRef,
                              readSTRef,
                              freeSTRef,
                              module Control.Monad.Trans,
                              module Control.Monad.Identity,
                              M.join) where
import Prelude hiding (lookup)
import Control.Monad hiding (join)
import qualified Control.Monad as M
import Control.Applicative hiding (some, many, empty)
import qualified Control.Applicative as A
import Data.Functor
import Control.Monad.State.Strict hiding (join)
import Data.IntMap
import Control.Monad.Base
import Control.Monad.Trans
import Control.Monad.Identity hiding (join)
import Data.Pointed
import Data.Functor.Apply
import Data.Functor.Bind
import Data.Functor.Bind.Trans
import Data.Functor.Alt hiding (some, many)
import qualified Data.Functor.Alt as B
import Data.Typeable
import Control.Monad.Fix
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.Cont.Class
import Control.Monad.Error.Class
import Data.StateRef.Types
import Data.Maybe
import Control.Monad.Trans.State.Strict (liftCallCC)
import Data.Monoid hiding (Any)
import Unsafe.Coerce
import GHC.Exts (Any)

newtype STT s m a = STT (StateT Con m a)

data Con = Con [Int] !(IntMap Any)

instance (Functor f) => Functor (STT s f) where
  fmap f (STT inner) = STT $ fmap f inner
  x <$ (STT inner) = STT $ x <$ inner

instance (Pointed f) => Pointed (STT s f) where
  point = STT . point

instance (Bind f, Monad f) => Apply (STT s f) where
  (STT innerM) <.> (STT innerQ) = STT $ innerM <.> innerQ
  (STT innerA) <. (STT innerB) = STT $ innerA <. innerB
  (STT innerA) .> (STT innerB) = STT $ innerA .> innerB

instance (Alt f, Bind f, MonadPlus f) => Alt (STT s f) where
  (STT innerA) <!> (STT innerB) = STT $ innerA <!> innerB
  some (STT inner) = STT $ B.some inner
  many (STT inner) = STT $ B.many inner

instance (Applicative f, Monad f) => Applicative (STT s f) where
  pure = STT . pure
  (STT innerM) <*> (STT innerQ) = STT $ innerM <*> innerQ
  (STT innerA) <* (STT innerB) = STT $ innerA <* innerB
  (STT innerA) *> (STT innerB) = STT $ innerA *> innerB

instance (Alternative f, MonadPlus f) => Alternative (STT s f) where
  empty = STT A.empty
  (STT innerA) <|> (STT innerB) = STT $ innerA <|> innerB
  some (STT inner) = STT $ A.some inner
  many (STT inner) = STT $ A.many inner

instance (Bind m, Monad m) => Bind (STT s m) where
  (STT inner0) >>- f = STT $ inner0 >>- (\x -> let (STT inner1) = f x in inner1)
  join (STT inner0) = STT . join $ fmap (\(STT inner1) -> inner1) inner0

instance (Monad m) => Monad (STT s m) where
  (STT inner0) >>= f = STT $ inner0 >>= (\x -> let (STT inner1) = f x in inner1)
  return = STT . return
  (STT innerA) >> (STT innerB) = STT $ innerA >> innerB
  fail = STT . fail

instance BindTrans (STT s) where
  liftB = STT . liftB

instance MonadTrans (STT s) where
  lift = STT . lift

instance (MonadBase b m) => MonadBase b (STT s m) where
  liftBase = STT . liftBase

instance (MonadPlus m) => MonadPlus (STT s m) where
  mzero = STT mzero
  (STT innerA) `mplus` (STT innerB) = STT $ innerA `mplus` innerB

instance (MonadFix m) => MonadFix (STT s m) where
  mfix f = STT . mfix $ \x -> let (STT inner) = f x in inner

instance (MonadReader r m) => MonadReader r (STT s m) where
  ask = STT ask
  local f (STT inner) = STT $ local f inner
  reader = STT . reader

instance (MonadCont m) => MonadCont (STT s m) where
  callCC f = STT . StateT $ \s -> callCC $ \c -> let (STT k) = f (\a -> STT . StateT $ \s' -> c (a, s')) in runStateT k s

instance (MonadError e m) => MonadError e (STT s m) where
  throwError = STT . throwError
  catchError (STT inner0) f = STT $ let g mq = (let (STT inner1) = f mq in inner1) in catchError inner0 g

instance (Monoid q, MonadWriter q m) => MonadWriter q (STT s m) where
  writer = STT . writer
  tell = STT . tell
  listen (STT inner) = STT $ listen inner
  pass (STT inner) = STT $ pass inner

instance (MonadState k m) => MonadState k (STT s m) where
  get = lift get
  put = lift . put
  state = lift . state

instance (MonadIO m) => MonadIO (STT s m) where
  liftIO = STT . liftIO

instance (Typeable s, Typeable1 m) => Typeable1 (STT s m) where
  typeOf1 _ = mkTyCon3 "pure-st" "Control.Monad.Pure.ST.Internals" "STT" `mkTyConApp` [typeOf (undefined :: s), typeOf1 (undefined :: m ())]

newtype STRef s a = STRef Int deriving (Typeable, Eq)

runSTT :: (Monad m) => (forall s. STT s m a) -> m a
runSTT (STT ist) = evalStateT ist (Con (concat $ zipWith (\a b -> [a, b]) [0, 1 .. maxBound] [(-1), (-2) .. minBound]) empty)

instance (Monad m) => WriteRef (STRef s a) (STT s m) a where
  writeReference (STRef i) x = STT . modify $ \(Con l v) -> Con l $ insert i ((unsafeCoerce :: a -> Any) x) v

instance (Monad m) => ReadRef (STRef s a) (STT s m) a where
  readReference (STRef i) = STT $ do Con l v <- get
                                     return . (unsafeCoerce :: Any -> a) . fromJust . lookup i $ v

instance (Monad m) => ModifyRef (STRef s a) (STT s m) a where
  modifyReference (STRef i) f = STT . modify $ \(Con l v) -> Con l $ adjust ((unsafeCoerce :: a -> Any) . f . (unsafeCoerce :: Any -> a)) i v
  atomicModifyReference = defaultAtomicModifyReference

instance (Monad m) => NewRef (STRef s a) (STT s m) a where
  newReference x = STT $ do Con (i:is) v <- get
                            put $ Con is $ insert i ((unsafeCoerce :: a -> Any) x) v
                            return (STRef i :: STRef s a)

freeSTRef :: (Monad m) => STRef s a -> STT s m ()
freeSTRef (STRef i) = STT . modify $ \(Con l v) -> Con (i:l) (delete i v)

instance (Monad m) => HasRef (STT s m) where
  newRef (x :: a) = liftM Ref (newReference x :: STT s m (STRef s a))

type ST s = STT s Identity

runST :: (forall s. ST s a) -> a
runST = runIdentity . runSTT

fixST :: (a -> ST s a) -> ST s a
fixST = mfix

fixSTT :: (MonadFix m) => (a -> STT s m a) -> STT s m a
fixSTT = mfix

writeSTRef :: (Monad m) => STRef s a -> a -> STT s m ()
writeSTRef = writeReference

readSTRef :: (Monad m) => STRef s a -> STT s m a
readSTRef = readReference

modifySTRef :: (Monad m) => STRef s a -> (a -> a) -> STT s m ()
modifySTRef = modifyReference

newSTRef :: (Monad m) => a -> STT s m (STRef s a)
newSTRef = newReference
