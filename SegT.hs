module MyLib.SegT where

import Data.List
import Data.Bits
--import Data.Array
import Data.Array.Unboxed
import Data.Array.MArray
import Data.Array.ST
import Control.Monad
import Control.Monad.ST
--import Debug.Trace

main :: IO ()
main = print $ runST $ do
  segT <- buildSegT [2,3,5,7]
  test1 <- forM [1..7] $ \ i -> readArray segT i
  test2 <- readRSegT segT (2,3)
  return (test1,test2)

type Elem = Int
type SegT s = STUArray s Int Elem
--モノイドの単位元
identity :: Elem
identity = 1

--モノイドの演算
(><) :: Elem -> Elem -> Elem
(><) = (*)

{-
セグ木について
sup2によりnを２の冪にする
配列をdp[1]~[n] 変数はi'
セグ木をsegT[1]~[2*n-1] 変数はi
添え字iに対して、親ノードはi`div`2、子ノードは2*i,2*i+1
高さは (ceiling $ logBase 2 (fromIntegral i))
それぞれ関数名のPは一点、Rは範囲の操作
-}

--nを超える最小の２の冪
sup2 :: Int -> Int
sup2 n = 2^(ceiling $ logBase 2 (fromIntegral n :: Double) :: Int)

newSegT :: MArray a e m => Int -> e -> m (a Int e)
newSegT n e = newArray (1,2*n-1) e

buildSegT :: [Elem] -> ST s (SegT s)
buildSegT ls = do
  let n = length ls
  segT <- newSegT n identity
  forM_ (zip [n..2*n-1] ls) $ \(i,e) -> writeArray segT i e
  rebuildSegT segT
  return segT

rebuildSegT :: SegT s -> ST s Elem
rebuildSegT segT = do
  n <- (`div`2).(+1).snd <$> getBounds segT
  sub segT n 1
  where
    sub :: SegT s -> Int -> Int -> ST s Elem
    sub segT' n' i
      | i >= n' = readArray segT' i
      | otherwise = do
        vl <- sub segT' n' (2*i)
        vr <- sub segT' n' (2*i+1)
        writeArray segT' i $ {-mod'-} (vl >< vr)
        return ${- mod'-} (vl >< vr)

--logN
modifyPSegT  :: SegT s -> Int -> Elem -> ST s ()
modifyPSegT segT i e = do
  n <- (`div`2).(+1).snd <$> getBounds segT
  writeArray segT (n+i-1) e
  sub segT (n+i-1)
  where
    sub :: SegT s -> Int -> ST s ()
    sub segT i
      | 1 >= i = return ()
      | otherwise = do
        a <- readArray segT i
        b <- readArray segT (if even i then i+1 else i-1)
        writeArray segT (i`div`2) (a >< b)
        sub segT (i`div`2)

--セグ木の読み込み
--(left,right)の範囲
readRSegT :: SegT s -> (Int,Int) -> ST s Elem
readRSegT segT (left,right) = do
  bnds <- getBounds segT
  sub segT (left,right) (fst bnds, (1+(snd bnds))`div`2) 1
  where
    sub :: SegT s -> (Int,Int) -> (Int,Int) -> Int -> ST s Elem
    sub segT (left,right) (l,r) i
      | r < left || right < l = return identity
      | left <= l && r <= right = do
        readArray segT i
      | otherwise  = do
        let mid = (l+r)`div`2
        vr <- sub segT (left,right) (mid+1,r) (2*i+1)
        vl <- sub segT (left,right) (l,mid) (2*i)
        return $ vr >< vl
