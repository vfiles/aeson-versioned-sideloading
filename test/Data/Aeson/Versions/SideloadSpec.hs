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

module Data.Aeson.Versions.SideloadSpec where

import Test.Hspec

import Data.Aeson
import Data.Aeson.Versions
import Data.Aeson.Versions.Sideload

import qualified Data.Map as M

import Data.Tagged

newtype UserId = UserId Integer deriving (Ord, Eq, Show)
newtype VfileId = VfileId Integer deriving (Ord, Eq, Show)
newtype MediaId = MediaId Integer deriving (Ord, Eq, Show)

instance ToJSON UserId where
    toJSON (UserId uid) = Number (fromInteger uid)

instance ToJSON MediaId where
    toJSON (MediaId pid) = Number (fromInteger pid)

instance ToJSON VfileId where
    toJSON (VfileId pid) = Number (fromInteger pid)


data User = User { userId :: UserId
                 , userName :: String
                 } deriving (Show)

type instance Id User = UserId
type instance EntityName User = "User"

data Media = Media { mediaId :: MediaId
                   , mediaOwner :: UserId
                   , mediaCaption :: String
                   } deriving (Show)

type instance Id Media = MediaId
type instance EntityName Media = "Media"

instance ToJSON (Tagged V1 Media) where
    toJSON (Tagged (Media mid pid cap)) = object [ "mediaId" .= mid
                                                 , "ownerId" .= pid
                                                 , "caption" .= cap
                                                 ]

instance Inflatable '[User] Media where
    type Support Media = '[ '(V1, '[ '( Media, V1)
                                   , '( User, V1)
                                   ]
                             )
                          , '(V2, '[ '( Media, V1)
                                   , '( User, V1)
                                   ]
                             )
                          ]

    dependencies (Media mid pid cap) = [pid] :-: DependenciesNil

    inflaters _ = inflatePerson :^: InflateNil
        where inflatePerson pid = return $ User pid "ben"


instance ToJSON (Tagged V1 User) where
    toJSON (Tagged (User pid name)) = object [ "id" .= pid
                                             , "name" .= name
                                             ]


data Vfile = Vfile { vfileId :: VfileId
                   , vfileOwner :: UserId
                   , vfileTitle :: String
                   , vfileMedia :: [MediaId]
                   }

instance ToJSON (Tagged V1 Vfile) where
    toJSON (Tagged (Vfile vid mid title mids)) = object [ "vfileId" .= vid
                                                        , "ownerId" .= mid
                                                        , "title" .= title
                                                        , "media" .= mids
                                                        ]

type instance Id Vfile = VfileId
type instance EntityName Vfile = "Vfile"

instance Inflatable '[User, Media] Vfile where
    type Support Vfile = '[ '(V1, '[ '(Vfile, V1), '(User, V1), '(Media, V1)])]

    dependencies (Vfile _ pid _ mids) = [pid] :-: mids :-: DependenciesNil

    inflaters _ = inflatePerson :^: inflateMedia :^: InflateNil
        where inflatePerson pid = return $ User pid "ben"
              inflateMedia mid = return $ Media mid (UserId 1) "caption"

someMedia :: Media
someMedia = Media (MediaId 1) (UserId 1) "caption"

someVfile :: Vfile
someVfile = Vfile (VfileId 1) (UserId 1) "vfile title" [MediaId 1, MediaId 2]


spec :: Spec
spec = do
  describe "serializers" $ do
    it "does the dependencies" $ do
      inflated <- inflate someMedia
      case mToJSON (Tagged @V1 inflated) of
        Just value -> return ()
        Nothing -> error "failed to serialize!"
