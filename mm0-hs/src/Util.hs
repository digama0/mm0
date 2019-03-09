module Util where

import qualified Data.Map.Strict as M
import Control.Monad.Except

fromJustError :: MonadError e m => e -> Maybe a -> m a
fromJustError errorval Nothing = throwError errorval
fromJustError _ (Just normalval) = return normalval

guardError :: MonadError e m => e -> Bool -> m ()
guardError _ True = return ()
guardError e _ = throwError e

insertNew :: (Ord k, MonadError e m) => e -> k -> v -> M.Map k v -> m (M.Map k v)
insertNew e k v m = do
  guardError e (M.notMember k m)
  return (M.insert k v m)
