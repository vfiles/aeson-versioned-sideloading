{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.Aeson.Versions.Sideload where

import Control.Arrow
import Control.Monad
import Control.Monad.IO.Class

import Control.Error

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Versions
import Data.Aeson.Versions.Internal

import Data.Proxy
import Data.Tagged

import Data.Foldable

import Data.Singletons
import Data.Singletons.Prelude hiding (Id)

import Data.Monoid

import qualified Data.Text as T

import qualified Data.Map as M

import GHC.Exts
import GHC.TypeLits

------------------
-- Library Code --
------------------

type family Id (a :: *) :: *
type family EntityName (a :: *) :: Symbol

infixr `EntityMapCons`

data EntityMapList (l :: [*]) where
    EntityMapNil :: EntityMapList '[]
    EntityMapCons :: M.Map (Id a) a -> EntityMapList ls -> EntityMapList (a ': ls )

deriving instance (AllSatisfy (TyCon1 Eq) ks, AllSatisfy (TyCon1 Eq :.$$$ Id') ks) => (Eq (EntityMapList ks))
deriving instance (AllSatisfy Show' ks, AllSatisfy (Show' :.$$$ Id') ks) => (Show (EntityMapList ks))

data SMap :: [(a, b)] -> * where
   SMapNil :: SMap '[]
   SMapCons :: Proxy a -> Proxy b -> SMap xs -> SMap ( '(a, b) ': xs )

type family AllSatisfyKV (cf :: TyFun k (TyFun v Constraint -> *) -> *) (xs :: [(k, v)]) :: Constraint where
    AllSatisfyKV cf '[] = ()
    AllSatisfyKV cf ( '(k, v) ': xs ) = (Apply (Apply cf k) v, AllSatisfyKV cf xs)

type family Keys (xs :: [(a, b)]) :: [a] where
    Keys '[] = '[]
    Keys ('(k, v) ': xs) = k ': Keys xs

type family Values (xs :: [(a, b)]) :: [b] where
    Values '[] = '[]
    Values ('(k, v) ': xs) = v ': Values xs

type family DepsMatch (deps :: [a]) (depMap :: [(a, b)]) :: Constraint where
    DepsMatch deps depMap = Keys depMap ~ deps

serializeEntityMapList :: forall depMap.
                          (AllSatisfyKV (HasVersion'' FailableToJSON) depMap
                          ,AllSatisfy (Show' :.$$$ Id') (Keys depMap)
                          ,AllSatisfy (KnownSymbol' :.$$$ EntityName') (Keys depMap)
                          ) =>
                          SMap depMap -> EntityMapList (Keys depMap) -> Maybe [Pair]
serializeEntityMapList SMapNil EntityMapNil = Just []
serializeEntityMapList (SMapCons (_ :: Proxy e) (_ :: Proxy v) restMap) (EntityMapCons eMap rest) = do
      let mserialized = mToJSON . (\a -> Tagged a :: Tagged v e) <$> eMap
      mserialized' <- M.toList . M.mapKeys show <$> sequence mserialized
      let mserialized'' = first T.pack <$> mserialized'
      restSerialized <- serializeEntityMapList restMap rest
      return $ (T.pack . symbolVal $ (Proxy :: Proxy (EntityName e)), object mserialized'') : restSerialized

class KnownMap (keyMap :: [(a, b)]) where
    mapSing :: SMap keyMap

instance KnownMap '[] where
    mapSing = SMapNil

instance KnownMap xs => KnownMap ( '(a, b) ': xs ) where
    mapSing = SMapCons Proxy Proxy mapSing

data Full deps a  = Full a (EntityMapList deps)

infixr :^:

data InflateList :: (* -> *) -> [*] -> * where
  InflateNil :: InflateList m '[]
  (:^:) :: (Id a -> m (Maybe a)) -> InflateList m as -> InflateList m (a ': as)
  (:^^:) :: ([Id a] -> m [(Id a, a)]) -> InflateList m as -> InflateList m ( a ': as )

infixr :-:

data DependenciesList :: [*] -> * where
  DependenciesNil :: DependenciesList '[]
  (:-:) :: [Id a] -> DependenciesList as -> DependenciesList ( a ': as)

instance Monoid (DependenciesList '[]) where
  mempty = DependenciesNil
  mappend _ _ = DependenciesNil

instance Monoid (DependenciesList deps) => Monoid (DependenciesList ( d ': deps)) where
  mempty = mempty :-: mempty
  mappend (a :-: restA) (b :-: restB) = (a <> b) :-: (restA <> restB)


class (AllSatisfy (DepsMatch' (a ': deps)) (Values (Support a))) => Inflatable deps a where
    type Support a :: [(Version Nat Nat, [(*, Version Nat Nat)])]
    type InflateC a :: (* -> *) -> Constraint
    type InflateC a = MonadIO
    dependencies :: a -> DependenciesList deps
    inflaters :: forall m . (InflateC a m) => Proxy a -> InflateList m deps

type family SupportBase a where
  SupportBase (t a) = Support a
  SupportBase a = Support a

type family InflateCBase a where
  InflateCBase (t a) = InflateC a
  InflateCBase a = InflateC a

class (AllSatisfy (DepsMatch' (baseType ': deps)) (Values (SupportBase a))) => InflatableBase deps baseType a where
    dependenciesBase :: Proxy baseType -> a -> DependenciesList deps
    inflatersBase :: forall m . (InflateCBase a m) => Proxy baseType -> Proxy a -> InflateList m deps


instance {-# OVERLAPPABLE #-} (AllSatisfy (DepsMatch' (a ': deps)) (Values (SupportBase a))
         ,Inflatable deps a, InflateCBase a ~ InflateC a) => InflatableBase deps a a where
    dependenciesBase _ = dependencies
    inflatersBase _ = inflaters


instance {-# OVERLAPPABLE #-} (AllSatisfy (DepsMatch' (a ': deps)) (Values (SupportBase (t a)))
         ,InflatableBase deps a a
         ,InflateCBase a ~ InflateC a
         ,Functor t
         ,Foldable t
         ,Monoid (DependenciesList deps)) => InflatableBase deps a (t a) where

  inflatersBase pBase _ = inflatersBase pBase (Proxy :: Proxy a)

  dependenciesBase pBase = fold . fmap (dependenciesBase pBase)

makeEntityMapList :: forall xs m.
                     (AllSatisfy (Ord' :.$$$ Id') xs, Monad m) =>
                     InflateList m xs -> DependenciesList xs -> m (EntityMapList xs)
makeEntityMapList InflateNil DependenciesNil = return EntityMapNil
makeEntityMapList (inflater :^: restInflate) (dependencies' :-: restDepends) = do
  these <- forM dependencies' $ \eid -> runMaybeT $ do
    inflated <- MaybeT $ inflater eid
    return (eid, inflated)
  rest <- makeEntityMapList restInflate restDepends
  return $ EntityMapCons (M.fromList  $ catMaybes these) rest
makeEntityMapList (inflater :^^: restInflate) (dependencies' :-: restDepends) = do
  these <- inflater dependencies'
  rest <- makeEntityMapList restInflate restDepends
  return $ EntityMapCons (M.fromList these) rest


inflateP :: forall deps baseType a m.
            (Monad m, InflateCBase a m, InflatableBase deps baseType a, AllSatisfy (Ord' :.$$$ Id') deps) =>
            Proxy baseType -> a -> m (Full deps a)
inflateP _ a = Full a <$> makeEntityMapList (inflatersBase (Proxy :: Proxy baseType) (Proxy :: Proxy a)) (dependenciesBase (Proxy :: Proxy baseType) a)

inflate :: forall deps baseType a m.
           (Monad m, InflateCBase a m, InflatableBase deps baseType a, AllSatisfy (Ord' :.$$$ Id') deps)
           => a -> m (Full deps a)
inflate a = Full a <$> makeEntityMapList (inflatersBase (Proxy :: Proxy baseType) (Proxy :: Proxy a)) (dependenciesBase (Proxy :: Proxy baseType) a)

type family Lookup (x :: k) (xs :: [(k, v)])  :: Maybe v where
    Lookup x '[] = 'Nothing
    Lookup x ( '(x, v) ': xs ) = 'Just v
    Lookup x ( '(y, v) ': ys ) = Lookup x ys

instance {-# OVERLAPPABLE #-} ( InflatableBase depTypes a a
         -- ^ main type is inflatable
         , Keys (Tail deps) ~ depTypes
         , KnownMap (Tail deps)
         , Lookup v (SupportBase a) ~ 'Just deps
         -- ^ version of inflated type is supported
         , Lookup a deps ~ 'Just mainV
         , FailableToJSON (Tagged mainV a)
         -- ^ get version of uninflated type and make sure that it's serializable
         , AllSatisfyKV (HasVersion'' FailableToJSON) (Tail deps)
         -- ^ all dependencies are versioned
         , AllSatisfy (Show' :.$$$ Id') depTypes
         -- ^ all entities have showable ids
         , AllSatisfy (KnownSymbol' :.$$$ EntityName') depTypes
         -- ^ all entities have names
         ) => FailableToJSON (Tagged v (Full depTypes a)) where
    mToJSON (Tagged (Full a entities)) = do
      skeletonJSON <- mToJSON (Tagged a :: Tagged mainV a)
      depsPairs <- serializeEntityMapList (mapSing :: SMap (Tail deps)) entities
      return . object $ [ "data" .= skeletonJSON
                        , "depdencies" .= object depsPairs
                        ]

instance ( InflatableBase depTypes a (t a)
         , Functor t
         , Foldable t
         , CatMaybes t
         , FunctorToJSON t
         -- ^ main type is inflatable
         , Keys (Tail deps) ~ depTypes
         , KnownMap (Tail deps)
         , Lookup v (SupportBase (t a)) ~ 'Just deps
         -- ^ version of inflated type is supported
         , Lookup a deps ~ 'Just mainV
         , FailableToJSON (Tagged mainV a)
         -- ^ get version of uninflated type and make sure that it's serializable
         , AllSatisfyKV (HasVersion'' FailableToJSON) (Tail deps)
         -- ^ all dependencies are versioned
         , AllSatisfy (Show' :.$$$ Id') depTypes
         -- ^ all entities have showable ids
         , AllSatisfy (KnownSymbol' :.$$$ EntityName') depTypes
         -- ^ all entities have names
         ) => FailableToJSON (Tagged v (Full depTypes (t a))) where
    mToJSON (Tagged (Full a entities)) = do
      skeletonJSON <- runSerializer mToJSON $ (\e -> (Tagged e :: Tagged mainV a)) <$> a
      depsPairs <- serializeEntityMapList (mapSing :: SMap (Tail deps)) entities
      return . object $ [ "data" .= skeletonJSON
                        , "depdencies" .= object depsPairs
                        ]



data ProxyList :: [k] -> * where
  ProxyNil :: ProxyList '[]
  ProxyCons :: Proxy k -> ProxyList ks -> ProxyList ( k ': ks )

class KnownList (xs :: [k]) where
    getProxyList :: ProxyList xs

instance KnownList '[] where
    getProxyList = ProxyNil

instance KnownList ks => KnownList (k ': ks) where
    getProxyList = ProxyCons Proxy getProxyList

collapseProxyList :: forall vs a .
                     (AllSatisfy KnownVersion' vs
                     ,AllSatisfy (HasVersion' FailableToJSON a) vs
                     ) =>
                     ProxyList (vs :: [Version Nat Nat]) -> [(Version Integer Integer, Serializer a)]
collapseProxyList ProxyNil = []
collapseProxyList (ProxyCons p rest) = (getSerializer p) : (collapseProxyList rest)

instance (InflatableBase deps baseType a
         ,vs ~ Keys (SupportBase a)
         ,KnownList vs
         ,AllSatisfy KnownVersion' vs
         ,AllSatisfy (HasVersion' FailableToJSON (Full deps a)) vs
         ,ToSerializerMap (Full deps a) vs
         ) => SerializedVersion (Full deps a) where
  type SerializerVersions (Full deps a) = Keys (SupportBase a)



---------------------------
-- *class boilerplate --
---------------------------

data HasVersion'' :: c -> (TyFun a (TyFun (Version Nat Nat) Constraint -> *) -> *)

type instance Apply (HasVersion'' c) a = HasVersion' c a

data DepsMatch' :: [a] -> TyFun [(a, b)] Constraint -> *

type instance Apply (DepsMatch' deps) depMap = DepsMatch deps depMap

data Show' :: TyFun a Constraint -> *

type instance Apply Show' a = Show a

data Id' :: TyFun a * -> *

type instance Apply Id' a = Id a

data Ord' :: TyFun a Constraint -> *

type instance Apply Ord' a = Ord a

data EntityName' :: TyFun a Symbol -> *

type instance Apply EntityName' a = EntityName a

data KnownSymbol' :: TyFun Symbol Constraint -> *

type instance Apply KnownSymbol' a = KnownSymbol a

data KnownVersion' :: TyFun (Version Nat Nat) Constraint -> *

type instance Apply KnownVersion' v = KnownVersion v
