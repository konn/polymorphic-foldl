{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

module Control.Foldl.Polymorphic (
  FolderM (..),
  Fold,
  FoldM,
  Fold1,
  FoldM1,
  fold,
  foldM,
  foldOver,
  fold1,
  foldM1,
  foldOver1,
  handles,
  handles1,
  folded,
  folded1,
  hoists,
  generalize,
  premapM,
  mapM,
  forM,
  dimapM,
  feedM,
  feed,
  list,
  nonEmpty,
  head,
  headMaybe,
  last,
  lastMaybe,
  sconcat,
  mconcat,
  sum,
  foldByKeyMap,
  duplicateM,
  CompactEndo (..),
  CompactEndoM (..),
  HandlerM1,
  Folder,
  Mode (..),
  L,
  L1,
  asFold1,
  weaken,
) where

import Control.Category (Category)
import qualified Control.Category as Cat
import Control.Foldl (EndoM (..), HandlerM, folded)
import Control.Monad ((<$!>), (<=<))
import qualified Data.DList.DNonEmpty as DLNE
import qualified Data.Foldable as F
import Data.Functor.Apply (Apply (..), WrappedApplicative (..))
import Data.Functor.Const
import Data.Functor.Contravariant (Contravariant (..))
import Data.Functor.Identity (Identity (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid (Ap (..), First (..), Last (..))
import Data.Profunctor (Profunctor (..))
import Data.Semigroup (Dual (..))
import Data.Semigroup.Foldable hiding (fold1)
import Data.Semigroupoid
import qualified Data.Strict as St
import qualified Data.Strict.Maybe as SMaybe
import Data.Strict.Tuple (Pair (..))
import GHC.Base hiding (mapM, mconcat, sconcat)
import GHC.Generics (Generic)
import Prelude hiding (head, last, mapM, mconcat, sum)

data Mode = L | L1
  deriving (Show, Eq, Ord, Generic)

type L = 'L

type L1 = 'L1

type role FolderM nominal representational representational nominal

type FolderM :: Mode -> (Type -> Type) -> Type -> Type -> Type
data FolderM mode m a b where
  FoldM :: (x -> a -> m x) -> m x -> (x -> m b) -> FolderM l m a b
  FoldM1 :: (x -> a -> m x) -> (a -> m x) -> (x -> m b) -> FolderM L1 m a b

instance Functor m => Functor (FolderM l m a) where
  fmap f = \case
    FoldM g mx h -> FoldM g mx (fmap f . h)
    FoldM1 g h fun -> FoldM1 g h (fmap f . fun)
  {-# INLINE fmap #-}

instance Apply m => Apply (FolderM l m a) where
  (FoldM f mx done) <.> (FoldM h mx' done') =
    FoldM
      (\(l :!: r) a -> (:!:) <$> f l a <.> h r a)
      ((:!:) <$> mx <.> mx')
      (\(g :!: x) -> done g <.> done' x)
  (FoldM f mx done) <.> (FoldM1 h mx' done') =
    FoldM1
      (\(l :!: r) a -> (:!:) <$> f l a <.> h r a)
      (\a -> (:!:) <$> mx <.> mx' a)
      (\(g :!: x) -> done g <.> done' x)
  (FoldM1 f mx done) <.> (FoldM h mx' done') =
    FoldM1
      (\(l :!: r) a -> (:!:) <$> f l a <.> h r a)
      (\a -> (:!:) <$> mx a <.> mx')
      (\(g :!: x) -> done g <.> done' x)
  (FoldM1 f mx done) <.> (FoldM1 h mx' done') =
    FoldM1
      (\(l :!: r) a -> (:!:) <$> f l a <.> h r a)
      (\a -> (:!:) <$> mx a <.> mx' a)
      (\(g :!: x) -> done g <.> done' x)

instance Applicative m => Applicative (FolderM l m a) where
  (<*>) = coerce $ (<.>) @(WrappedApplicative (FolderM l m a))
  {-# INLINE (<*>) #-}
  pure = FoldM (fmap (fmap getAp) mempty) (pure ()) . const . pure
  {-# INLINE pure #-}

instance (Applicative m, Semigroup w) => Semigroup (FolderM l m a w) where
  (<>) = liftA2 (<>)
  {-# INLINE (<>) #-}

instance (Applicative m, Monoid w) => Monoid (FolderM l m a w) where
  mempty = pure mempty
  {-# INLINE mempty #-}

type FoldM = Folder L

type FoldM1 = Folder L1

type Fold = Folder L

type Fold1 = Folder L1

type Folder mode = FolderM mode Identity

fold :: (Foldable t) => Fold a b -> t a -> b
fold (FoldM step begin done) as = F.foldr cons (coerce done) as (coerce begin)
  where
    cons a k x = k $! runIdentity (step x a)

foldByKeyMap ::
  forall k a b m l.
  (Monad m, Ord k) =>
  FolderM L1 m a b ->
  FolderM l m (k, a) (Map k b)
foldByKeyMap =
  \case
    FoldM1 (f :: x -> a -> m x) g h ->
      let step :: Map k x -> (k, a) -> m (Map k x)
          step dic (k, a) = Map.alterF addMap k dic
            where
              addMap Nothing = Just <$!> g a
              addMap (Just ex) = Just <$!> f ex a
       in FoldM step (pure Map.empty) (traverse h)
    FoldM (f :: x -> a -> m x) g h ->
      let step :: Map k x -> (k, a) -> m (Map k x)
          step dic (k, a) = Map.alterF addMap k dic
            where
              addMap Nothing = Just <$!> g
              addMap (Just ex) = Just <$!> f ex a
       in FoldM step (pure Map.empty) (traverse h)

foldM :: (Foldable t, Monad m) => FolderM L m a b -> t a -> m b
foldM (FoldM f mx g) as0 = do
  !x0 <- mx
  F.foldr' step' g as0 $! x0
  where
    step' a k x = do
      !x' <- f x a
      k x'

newtype CompactEndoM m x = CompactEndoM {appCompactEndoM :: SMaybe.Maybe x -> m x}

instance Monad m => Semigroup (CompactEndoM m x) where
  CompactEndoM f <> CompactEndoM g = CompactEndoM $ \mx -> do
    !y <- f mx
    z <- g $ SMaybe.Just y
    z `seq` pure z

sconcat :: (Semigroup w, Applicative m) => FolderM L1 m w w
{-# INLINE sconcat #-}
sconcat = FoldM1 (fmap pure . (<>)) pure pure

mconcat :: (Monoid w, Applicative m) => FolderM l m w w
{-# INLINE mconcat #-}
mconcat = FoldM (fmap pure . (<>)) (pure mempty) pure

foldM1 :: (Foldable1 t, Monad m) => FolderM l m a b -> t a -> m b
foldM1 (FoldM step ini done) t = foldM (FoldM step ini done) t
foldM1 (FoldM1 step ini done) t =
  done
    =<< appCompactEndoM
      ( foldMap1
          ( \ !a -> CompactEndoM $ \case
              SMaybe.Nothing -> ini a
              SMaybe.Just x -> step x a
          )
          t
      )
      SMaybe.Nothing

newtype CompactEndo x = CompactEndo {appCompactEndo :: SMaybe.Maybe x -> x}

instance Semigroup (CompactEndo x) where
  CompactEndo f <> CompactEndo g = CompactEndo $ \mx ->
    let !y = f mx
        !z = g $ SMaybe.Just y
     in z

fold1 :: (Foldable1 t) => Folder l a b -> t a -> b
{-# INLINE fold1 #-}
fold1 (FoldM step ini done) t = fold (FoldM step ini done) t
fold1 (FoldM1 step ini done) t =
  runIdentity $
    done $
      appCompactEndo
        ( foldMap1
            ( \ !a -> CompactEndo $ \case
                SMaybe.Nothing -> runIdentity (ini a)
                SMaybe.Just x -> runIdentity (step x a)
            )
            t
        )
        SMaybe.Nothing

headMaybe :: Applicative m => FolderM l m a (Maybe a)
{-# INLINE headMaybe #-}
headMaybe = FoldM (dimap (First . Just) pure . (<>)) (pure mempty) (pure . getFirst)

lastMaybe :: Applicative m => FolderM l m a (Maybe a)
{-# INLINE lastMaybe #-}
lastMaybe = FoldM (dimap (Last . Just) pure . (<>)) (pure mempty) (pure . getLast)

head :: Applicative m => FolderM L1 m a a
{-# INLINE head #-}
head = FoldM1 (const . pure) pure pure

last :: Applicative m => FolderM L1 m a a
{-# INLINE last #-}
last = FoldM1 (const pure) pure pure

duplicateM :: Applicative m => FolderM l m a b -> FolderM l m a (FolderM L m a b)
duplicateM (FoldM f mx g) = FoldM f mx (\x -> pure (FoldM f (pure x) g))
duplicateM (FoldM1 f g h) = FoldM1 f g $ \x -> pure $ FoldM f (pure x) h

asFold1 :: FolderM l m a b -> FolderM L1 m a b
asFold1 (FoldM f mx g) = FoldM1 f (const mx) g
asFold1 f@FoldM1 {} = f

weaken :: Applicative m => FolderM l m a b -> FolderM L m a (Maybe b)
weaken (FoldM f mx g) = FoldM f mx (fmap Just . g)
weaken (FoldM1 f g (h :: x -> m b)) =
  FoldM step' (pure $ StNothing @x) (fmap St.toLazy . traverse h)
  where
    step' = \case
      StNothing -> fmap StJust . g
      StJust x -> fmap StJust . f x

instance Functor m => Profunctor (FolderM l m) where
  dimap f g =
    \case
      (FoldM h mx fun) -> FoldM (lmap f . h) mx (fmap g . fun)
      (FoldM1 h fun f') -> FoldM1 (lmap f . h) (fun . f) (fmap g . f')
  {-# INLINE dimap #-}
  lmap f =
    \case
      (FoldM h mx fun) -> FoldM (lmap f . h) mx fun
      (FoldM1 h fun f') -> FoldM1 (lmap f . h) (fun . f) f'
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}

dimapM :: Monad m => (a' -> m a) -> (b -> m b') -> FolderM l m a b -> FolderM l m a' b'
{-# INLINE dimapM #-}
dimapM f g =
  \case
    (FoldM h mx fun) -> FoldM (\x a' -> do !a <- f a'; h x a) mx (g <=< fun)
    (FoldM1 h mx fun) -> FoldM1 (\x a' -> do !a <- f a'; h x a) (mx <=< f) (g <=< fun)

premapM :: Monad m => (a' -> m a) -> FolderM l m a b -> FolderM l m a' b
{-# INLINE premapM #-}
premapM f =
  \case
    (FoldM h mx fun) -> FoldM (\x a' -> do !a <- f a'; h x a) mx fun
    (FoldM1 h mx fun) -> FoldM1 (\x a' -> do !a <- f a'; h x a) (mx <=< f) fun

mapM :: Monad m => (b -> m b') -> FolderM l m a b -> FolderM l m a b'
{-# INLINE mapM #-}
mapM g =
  \case
    (FoldM h mx fun) -> FoldM h mx (g <=< fun)
    (FoldM1 h mx fun) -> FoldM1 h mx (g <=< fun)

forM :: Monad m => FolderM l m a b -> (b -> m b') -> FolderM l m a b'
{-# INLINE forM #-}
forM = flip mapM

hoists :: (forall x. m x -> n x) -> FolderM l m a b -> FolderM l n a b
{-# INLINE hoists #-}
hoists h =
  \case
    (FoldM f mx g) -> FoldM (fmap h . f) (h mx) (h . g)
    (FoldM1 f g fun) -> FoldM1 (fmap h . f) (h . g) (h . fun)

foldOver :: Monad m => HandlerM m s a -> FolderM L m a b -> s -> m b
foldOver l (FoldM step begin done) s = do
  !b <- begin
  !r <-
    flip appEndoM b $!
      getDual $!
        getConst $!
          l (Const . Dual . EndoM . flip step) s
  done r
{-# INLINEABLE foldOver #-}

type HandlerM1 m a b =
  forall x.
  (b -> Const (CompactEndoM m x) b) ->
  a ->
  Const (CompactEndoM m x) a

list :: Applicative m => FolderM l m a [a]
{-# INLINE list #-}
list = FoldM (\x a -> pure $ x . (a :)) (pure id) (pure . ($ []))

nonEmpty :: Applicative m => FolderM L1 m a (NonEmpty a)
{-# INLINE nonEmpty #-}
nonEmpty = FoldM1 (dimap DLNE.singleton pure . (<>)) (pure . DLNE.singleton) (pure . DLNE.toNonEmpty)

feedM :: Monad m => FolderM L m a b -> a -> m (FolderM L m a b)
{-# INLINE feedM #-}
feedM l = foldM (duplicateM l) . Identity

feed :: Folder L a b -> a -> Folder L a b
{-# INLINE feed #-}
feed l = fold (duplicateM l) . Identity

generalize :: Applicative m => Folder l a b -> FolderM l m a b
{-# INLINE generalize #-}
generalize = hoists (pure . runIdentity)

-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> foldOver1 folded1 sum $ 20 :| [1..5]
-- 35

-- | Scanning the intermediate result of the second and feed it to the first.
instance Monad m => Semigroupoid (FolderM l m) where
  o :: FolderM l m j k -> FolderM l m i j -> FolderM l m i k
  o (FoldM f mx done) (FoldM f' mx' done') =
    FoldM
      ( \(x :!: y) a -> do
          !y' <- f' y a
          !j <- done' y'
          !x' <- f x j
          pure $! (x' :!: y')
      )
      ((:!:) <$!> mx <*> mx')
      (done . St.fst)
  o (FoldM f mx done) (FoldM1 f' fun done') =
    FoldM1
      ( \(x :!: y) a -> do
          !y' <- f' y a
          !j <- done' y'
          !x' <- f x j
          pure $! (x' :!: y')
      )
      (\i -> (:!:) <$!> mx <*> fun i)
      (done . St.fst)
  o (FoldM1 f (mx :: j -> m x) done) (FoldM f' (mx' :: m y) done') =
    FoldM
      ( \(x :!: y) i -> do
          !y' <- f' y i
          !j <- done' y'
          !x' <- f x j
          pure $! (x' :!: y')
      )
      ( do
          !y <- mx'
          !j <- done' y
          !x <- mx j
          pure $ x :!: y
      )
      (done . St.fst)
  o (FoldM1 f mx done) (FoldM1 f' mx' done') =
    FoldM1
      ( \(x :!: y) a -> do
          !y' <- f' y a
          !j <- done' y'
          !x' <- f x j
          pure $! (x' :!: y')
      )
      ( \i -> do
          !y <- mx' i
          !j <- done' y
          !x <- mx j
          pure $! (x :!: y)
      )
      (done . St.fst)

instance (Monad m, l ~ 'L1) => Category (FolderM l m) where
  id = last
  {-# INLINE id #-}
  (.) = o
  {-# INLINE (.) #-}

foldOver1 :: Monad m => HandlerM1 m s a -> FolderM l m a b -> s -> m b
foldOver1 l (viewFoldM1 -> AFoldM1 step begin done) s = do
  !r <-
    flip appCompactEndoM SMaybe.Nothing
      $! getConst
      $! l
        ( Const
            . CompactEndoM
            . flip
              ( \case
                  SMaybe.Nothing -> begin
                  SMaybe.Just x -> step x
              )
        )
      $! s
  done r
{-# INLINEABLE foldOver1 #-}

handles :: HandlerM m a b -> FolderM L m b r -> FolderM L m a r
handles k (FoldM step begin done) = FoldM step' begin done
  where
    step' = flip (appEndoM . getDual . getConst . k (Const . Dual . EndoM . flip step))

type StMaybe = SMaybe.Maybe

pattern StJust :: a -> StMaybe a
pattern StJust a = SMaybe.Just a

pattern StNothing :: StMaybe a
pattern StNothing = SMaybe.Nothing

{-# COMPLETE StJust, StNothing #-}

folded1 :: (Contravariant f, Apply f, Foldable1 t) => (a -> f a) -> t a -> f (t a)
{-# INLINE folded1 #-}
folded1 = fmap (() >$) . traverse1_

sum :: (Num a, Applicative m) => FolderM l m a a
{-# INLINE sum #-}
sum = FoldM (fmap pure . (+)) (pure 0) pure

{-

>>> fold1 (handles1 folded1 list) $ (9 :| [1,2,3]) :| [4 :| [], 5 :| [6..8]]
[9,1,2,3,4,5,6,7,8]

>>> fold (handles1 folded1 list) $ [10 :| [1,2,3], 4 :| [], 5 :| [6..8]]
[10,1,2,3,4,5,6,7,8]
-}

data AFoldM1 m a b where
  AFoldM1 :: (x -> a -> m x) -> (a -> m x) -> (x -> m b) -> AFoldM1 m a b

viewFoldM1 :: Monad m => FolderM l m a b -> AFoldM1 m a b
viewFoldM1 =
  \case
    (FoldM step mx done) ->
      AFoldM1 step (\ !a -> do !x <- mx; step x a) done
    (FoldM1 f g h) -> AFoldM1 f g h

handles1 :: forall l m a b r. HandlerM1 m a b -> FolderM l m b r -> FolderM l m a r
handles1 k (FoldM step begin done) = FoldM step' begin done
  where
    step' =
      flip
        ( appCompactEndoM
            . getConst
            . k
              ( Const . CompactEndoM . flip \case
                  StNothing -> const begin
                  StJust x -> step x
              )
        )
        . StJust
handles1 k (FoldM1 step (begin :: b -> m x) done) =
  FoldM1 (remap . StJust) (remap StNothing) done
  where
    remap =
      flip $
        appCompactEndoM
          . getConst
          . k
            ( Const . CompactEndoM . flip \case
                StNothing -> begin
                StJust x -> step x
            )
