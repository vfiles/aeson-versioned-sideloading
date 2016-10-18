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
{-# LANGUAGE PartialTypeSignatures #-}

module Data.Aeson.Versions.SideloadSpec where

import Test.Hspec

import Data.Aeson
import Data.Aeson.Versions
import Data.Aeson.Versions.Sideload

import Data.Functor.Identity

import qualified Data.Map as M

import Data.Tagged

import qualified Data.ByteString.Lazy.Char8 as B

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
                 } deriving (Eq, Show)

type instance Id User = UserId
type instance EntityName User = "User"

data Media = Media { mediaId :: MediaId
                   , mediaOwner :: UserId
                   , mediaCaption :: String
                   } deriving (Eq, Show)

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
                   } deriving (Eq, Show)

instance ToJSON (Tagged V1 Vfile) where
    toJSON (Tagged (Vfile vid mid title mids)) = object [ "vfileId" .= vid
                                                        , "ownerId" .= mid
                                                        , "title" .= title
                                                        , "mediaIds" .= mids
                                                        ]

type instance Id Vfile = VfileId
type instance EntityName Vfile = "Vfile"

instance Inflatable '[User, Media] Vfile where
    type Support Vfile = '[ '(V1, '[ '(Vfile, V1), '(User, V1), '(Media, V1)])]

    dependencies (Vfile _ pid _ mids) = [pid] :-: mids :-: DependenciesNil

    inflaters _ = inflatePerson :^: inflateMedia :^: InflateNil
        where inflatePerson pid = return $ User pid "ben"
              inflateMedia mid = return $ Media mid (UserId 1) "caption"


data FeedEvent = LikedVfile UserId VfileId
               | FiledMedia UserId MediaId VfileId deriving (Eq, Show)

instance ToJSON (Tagged V1 FeedEvent) where
  toJSON (Tagged (LikedVfile uid vid)) = object [ "type" .= ("LikedVfile" :: String)
                                                , "data" .= object
                                                  [ "userId" .= uid
                                                  , "vfileId" .= vid
                                                  ]
                                                ]
  toJSON (Tagged (FiledMedia uid mid vid)) = object [ "type" .= ("FiledMedia" :: String)
                                                    , "data" .= object
                                                      [ "userId" .= uid
                                                      , "mediaId" .= mid
                                                      , "vfileId" .= vid
                                                      ]
                                                    ]

instance Inflatable '[User, Media, Vfile] FeedEvent where
  type Support FeedEvent = '[ '(V1, '[ '(FeedEvent, V1)
                                     , '(User, V1)
                                     , '(Media, V1)
                                     , '(Vfile, V1)
                                     ])]
  dependencies (LikedVfile uid vid) = [uid] :-: [] :-: [vid] :-: DependenciesNil
  dependencies (FiledMedia uid mid vid) = [uid] :-: [mid] :-: [vid] :-: DependenciesNil


  inflaters _ = inflatePerson :^: inflateMedia :^: inflateVfile :^: InflateNil
      where inflatePerson pid = return $ User pid "ben"
            inflateMedia mid = return $ Media mid (UserId 1) "caption"
            inflateVfile vid = return $ Vfile vid (UserId 1) "vfile caption" [MediaId 1]

someMedia :: Media
someMedia = Media (MediaId 1) (UserId 1) "caption"

someVfile :: Vfile
someVfile = Vfile (VfileId 1) (UserId 1) "vfile title" [MediaId 1, MediaId 2]

someFeedEvents :: [FeedEvent]
someFeedEvents = [LikedVfile (UserId 1) (VfileId 1)
                 ,FiledMedia (UserId 1) (MediaId 1) (VfileId 1)
                 ]

spec :: Spec
spec = do
  describe "serializers" $ do
    it "does the dependencies" $ do
      inflated <- inflate someMedia
      case encode <$> mToJSON (Tagged inflated :: Tagged V1 _) of
        Just value -> B.putStrLn value
        Nothing -> error "failed to serialize!"
    it "does multiples!" $ do
      inflated <- inflate [someMedia]
      case encode <$> mToJSON (Tagged inflated :: Tagged V1 _) of
        Just value -> B.putStrLn value
        Nothing -> error "failed to serialize!"
    it "merges dependnecies properly" $ do
      inflated@(Full _ deps) <- inflate someFeedEvents
      deps `shouldBe` ((M.fromList [(UserId 1, User (UserId 1) "ben")])
                       `EntityMapCons`
                       (M.fromList [(MediaId 1, Media (MediaId 1) (UserId 1) "caption")])
                       `EntityMapCons`
                       (M.fromList [(VfileId 1, Vfile (VfileId 1) (UserId 1) "vfile caption" [MediaId 1])])
                       `EntityMapCons`
                       EntityMapNil
                      )
      case encode <$> mToJSON (Tagged inflated :: Tagged V1 _) of
        Just value -> B.putStrLn value
        Nothing -> error "failed to serialize!"
