module MM0.Util (module MM0.Util, module Debug.Trace, module GHC.Stack, (<&>)) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Writer
import Data.Word (Word8)
import Data.List (group, sort)
import Data.Functor
import Debug.Trace
import GHC.Stack
import System.Exit
import qualified Data.Text as T
import qualified Data.Char as C
import qualified Data.Map.Strict as M

fromMaybeM :: MonadPlus m => Maybe a -> m a
fromMaybeM Nothing = mzero
fromMaybeM (Just a) = return a

mapMaybeM :: Applicative m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM _ [] = pure []
mapMaybeM f (a : as) = liftA2 go (f a) (mapMaybeM f as) where
  go Nothing l = l
  go (Just b) l = b : l

fromJustError :: MonadError e m => e -> Maybe a -> m a
fromJustError errorval Nothing = throwError errorval
fromJustError _ (Just normalval) = return normalval

guardError :: MonadError e m => e -> Bool -> m ()
guardError _ True = return ()
guardError e _ = throwError e

withContext :: MonadError String m => T.Text -> m a -> m a
withContext s m = catchError m (\e -> throwError ("at " ++ T.unpack s ++ ": " ++ e))

insertNew :: (Ord k, MonadError e m) => e -> k -> v -> M.Map k v -> m (M.Map k v)
insertNew e k v m = do
  guardError e (M.notMember k m)
  return (M.insert k v m)

liftIO' :: Either String a -> IO a
liftIO' (Left e) = die e
liftIO' (Right e) = return e

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (a:_) = Just a

allUnique :: Ord a => [a] -> Bool
allUnique = all ((==) 1 . length) . group . sort

padL :: Int -> String -> String
padL n s
    | length s < n  = s ++ replicate (n - length s) ' '
    | otherwise = s

all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
all2 r = go where
  go [] [] = True
  go (a:as) (b:bs) = r a b && go as bs
  go _ _ = False

-- | Extract the written value of a writer action
extract :: MonadWriter w m => m a -> m (a, w)
extract m = censor (const mempty) (listen m)

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, y, _) = y

thd3 :: (a, b, c) -> c
thd3 (_, _, z) = z

toChar :: Word8 -> Char
toChar = C.chr . fromIntegral
