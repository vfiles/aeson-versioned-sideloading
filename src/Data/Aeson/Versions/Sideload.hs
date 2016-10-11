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
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Data.Aeson.Versions.Sideload where

import Control.Arrow
import Control.Monad

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Versions

import Data.Tagged

import Data.Singletons
import Data.Singletons.Prelude hiding (Id, Lookup)
import Data.Singletons.Prelude.Maybe

import Data.Kind

import qualified Data.Text as T

import qualified Data.ByteString.Lazy as B

import qualified Data.Map as M

import GHC.TypeLits

------------------
-- Library Code --
------------------

type family Id (a :: Type) :: Type
type family EntityName (a :: Type) :: Symbol

data EntityMapList (l :: [Type]) where
    EntityMapNil :: EntityMapList '[]
    EntityMapCons :: M.Map (Id a) a -> EntityMapList ls -> EntityMapList (a ': ls )

data SMap :: [(a, b)] -> Type where
   SMapNil :: SMap '[]
   SMapCons :: Proxy a -> Proxy b -> SMap xs -> SMap ( '(a, b) ': xs )

type family AllSatisfy (cf :: k ~> Constraint) (xs :: [k]) :: Constraint where
    AllSatisfy cf '[] = ()
    AllSatisfy cf ( x ': xs) = (Apply cf x, AllSatisfy cf xs)

type family AllSatisfyKV (cf :: k ~> v ~> Constraint) (xs :: [(k, v)]) :: Constraint where
    AllSatisfyKV cf '[] = ()
    AllSatisfyKV cf ( '(k, v) : xs ) = (Apply (Apply cf k) v, AllSatisfyKV cf xs)

type family Keys (xs :: [(a, b)]) :: [a] where
    Keys '[] = '[]
    Keys ('(k, v) ': xs) = k ': Keys xs

type family Values (xs :: [(a, b)]) :: [b] where
    Values '[] = '[]
    Values ('(k, v) ': xs) = v ': Values xs

type family DepsMatch (deps :: [a]) (depMap :: [(a, b)]) :: Constraint where
    DepsMatch deps depMap = Keys depMap ~ deps

type family HasVersion (cf :: Type -> Constraint) (e :: Type) (v :: Version Nat Nat) :: Constraint where
    HasVersion cf e v = cf (Tagged v e)

serializeEntityMapList :: forall depMap.
                          (AllSatisfyKV (HasVersion'' FailableToJSON) depMap
                          ,AllSatisfy (Show' :.$$$ Id') (Keys depMap)
                          ,AllSatisfy (KnownSymbol' :.$$$ EntityName') (Keys depMap)
                          ) =>
                          SMap depMap -> EntityMapList (Keys depMap) -> Maybe [Pair]
serializeEntityMapList SMapNil EntityMapNil = Just []
serializeEntityMapList (SMapCons (ep :: Proxy e) (vp :: Proxy v) restMap) (EntityMapCons eMap rest) = do
      let mserialized = mToJSON . Tagged @v <$> eMap
      mserialized' <- M.toList . M.mapKeys show <$> sequence mserialized
      let mserialized'' = first T.pack <$> mserialized'
      restSerialized <- serializeEntityMapList restMap rest
      return $ (T.pack . symbolVal $ Proxy @(EntityName e), object mserialized'') : restSerialized

class KnownMap (keyMap :: [(a, b)]) where
    mapSing :: SMap keyMap

instance KnownMap '[] where
    mapSing = SMapNil

instance KnownMap xs => KnownMap ( '(a, b) ': xs ) where
    mapSing = SMapCons Proxy Proxy mapSing

data Full deps a  = Full a (EntityMapList deps)

infixr :^:

data InflateList :: [Type] -> Type where
  InflateNil :: InflateList '[]
  (:^:) :: (Id a -> IO a) -> InflateList as -> InflateList ( a ': as )

infixr :-:

data DependenciesList :: [Type] -> Type where
  DependenciesNil :: DependenciesList '[]
  (:-:) :: [Id a] -> DependenciesList as -> DependenciesList ( a ': as)

class (AllSatisfy (DepsMatch' (a ': deps)) (Values (Support a))) => Inflatable deps a where
    type Support a :: [(Version Nat Nat, [(Type, Version Nat Nat)])]
    dependencies :: a -> DependenciesList deps
    inflaters :: Proxy a -> InflateList deps

makeEntityMapList :: forall xs .
                     (AllSatisfy (Ord' :.$$$ Id') xs) =>
                     InflateList xs -> DependenciesList xs -> IO (EntityMapList xs)
makeEntityMapList InflateNil DependenciesNil = return EntityMapNil
makeEntityMapList (inflater :^: restInflate) (dependencies' :-: restDepends) = do
  these <- forM dependencies' $ \eId -> do
             inflated <- inflater eId
             return (eId, inflated)
  rest <- makeEntityMapList restInflate restDepends
  return $ EntityMapCons (M.fromList these) rest

inflate :: forall deps a .
           (Inflatable deps a, AllSatisfy (Ord' :.$$$ Id') deps) => a -> IO (Full deps a)
inflate a = Full a <$> makeEntityMapList (inflaters (Proxy @a)) (dependencies a)

type family Lookup (x :: k) (xs :: [(k, v)])  :: Maybe v where
    Lookup x '[] = 'Nothing
    Lookup x ( '(x, v) ': xs ) = 'Just v
    Lookup x ( '(y, v) ': ys ) = Lookup x ys

instance ( Inflatable depTypes a
         -- ^ main type is inflatable
         , Keys (Tail deps) ~ depTypes
         , KnownMap (Tail deps)
         , Lookup v (Support a) ~ 'Just deps
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
      depsPairs <- serializeEntityMapList @(Tail deps) mapSing entities
      return . object $ [ "data" .= skeletonJSON
                        , "depdencies" .= object depsPairs
                        ]



data ProxyList :: [k] -> Type where
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

instance (Inflatable deps a
         ,vs ~ Keys (Support a)
         ,KnownList vs
         ,AllSatisfy KnownVersion' vs
         ,AllSatisfy (HasVersion' FailableToJSON (Full deps a)) vs
         ) => SerializedVersion (Full deps a) where
    serializers = let pList = getProxyList :: ProxyList vs
                  in M.fromList (collapseProxyList pList)



---------------------------
-- Typeclass boilerplate --
---------------------------

data  HasVersion' :: c -> a -> (Version Nat Nat ~> Constraint) where
  HasVersion' :: HasVersion' c a v

type instance Apply (HasVersion' c a) v = HasVersion c a v

data HasVersion'' :: c -> (a ~> (Version Nat Nat) ~> Constraint) where
  HasVersion'' :: HasVersion'' c a

type instance Apply (HasVersion'' c) a = HasVersion' c a

data HasVersionFlipped' :: c -> (Version Nat Nat) -> (a ~> Constraint) where
    HasVersionFlipped' :: HasVersionFlipped' c v a

type instance Apply (HasVersionFlipped' c v) a = HasVersion c a v

data DepsMatch' :: [a] -> TyFun [(a, b)] Constraint -> Type where
   DepsMatch' :: DepsMatch' deps depMap

type instance Apply (DepsMatch' deps) depMap = DepsMatch deps depMap

data Show' :: a ~> Constraint where
    Show' :: Show' a

type instance Apply Show' a = Show a

data Ord' :: a ~> Constraint where
    Ord' :: Ord' a

type instance Apply Ord' a = Ord a

data Id' :: a ~> Type where
    Id' :: Id' a

type instance Apply Id' a = Id a

data EntityName' :: a ~> Symbol where
    EntityName' :: EntityName' a

type instance Apply EntityName' a = EntityName a

data KnownSymbol' :: Symbol ~> Constraint where
  KnownSymbol' :: KnownSymbol' a

type instance Apply KnownSymbol' a = KnownSymbol a

data KnownVersion' :: Version Nat Nat ~> Constraint where
  KnownVersion' :: KnownVersion' v

type instance Apply KnownVersion' v = KnownVersion v
