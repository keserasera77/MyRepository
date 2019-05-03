module MyLib.SegT where

import Data.List
import Data.Bits
--import Data.Array
import Data.Array.Unboxed
import Data.Array.MArray
import Data.Array.ST
import Control.Monad
import Control.Monad.ST
import Debug.Trace

main :: IO ()
main = print $ runST $ do
  segT <- buildSegT [2,3,5,7]
  lazy <- newSegT 4 0
  modifyRSegT segT lazy (1,3)
  test1 <- forM [1..7] $ \ i -> readArray segT i
  test2 <- forM [1..7] $ \ i -> readArray lazy i
  test3 <- readRSegT segT lazy (2,3)
  test4 <- forM [1..7] $ \ i -> readArray segT i
  test5 <- forM [1..7] $ \ i -> readArray lazy i
  return (test1,test2,test3,test4,test5)

type Elem = Int
type SegT s = STUArray s Int Elem

--モノイドの単位元
identity :: Elem
identity = 10^9
--モノイドの演算
(><) :: Elem -> Elem -> Elem
(><) = min

--区間更新の操作は毎回同じことが仮定されている
func :: Elem -> Elem
func = (* 10)

nthfunc :: Int -> Elem -> Elem
nthfunc 0 a = a
nthfunc n a = nthfunc (n-1) (func a)

{-
セグ木について
sup2によりnを２の冪にする
配列をdp[1]~[n] 変数はi'
セグ木をsegT[1]~[2*n-1] 変数はi
添え字iに対して、親ノードはi`div`2、子ノードは2*i,2*i+1
高さは (ceiling $ logBase 2 (fromIntegral i))
関数名のP,Rはそれぞれ一点、範囲の操作
区間更新を行う場合は遅延評価用の別のセグ木を用意する必要がある。
遅延評価用のセグ木にはfuncによる更新の回数が記録されている。
・パターン1 func^n(a) >< func^m(b) == func^(n+m)(a >< b)  (n,m >= 0)
tochild == (`div`2)
newlanum == (r-l+1+lanum)
ex)
func = (*a)
(><) = (*)
・パターン2 func(a) >< func(b) == func(a >< b)
tochild == id
newlanum == 1+lanum
その場合例は下の通りになる
ex)
func = (+ const)
(><) = max
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


--使う場合は遅延評価用のセグ木を他に用意
modifyRSegT :: SegT s -> SegT s -> (Int,Int) -> ST s ()
modifyRSegT segT lazy (left,right) = do
  bnds <- getBounds lazy
  sub segT lazy (fst bnds, (1+(snd bnds))`div`2) 1
  return ()
  where
    sub :: SegT s -> SegT s -> (Int,Int) -> Int -> ST s Elem
    sub segT' lazy' (l,r) i
      | r < left || right < l = do
        lanum <- readArray lazy' i
        a <- readArray segT' i --更新後かチェック必要
        return $ nthfunc lanum a
      | left <= l && r <= right = do
        lanum <- readArray lazy' i
        let newlanum = 1+lanum  --(r-l+1+lanum) パターン２
        writeArray lazy' i newlanum
        a <- readArray segT' i
        return $ nthfunc newlanum a
      | otherwise  = do
        let mid = (l+r)`div`2
        a <- sub segT' lazy' (mid+1,r) (2*i+1)
        b <- sub segT' lazy' (l,mid) (2*i)
        writeArray segT' i (a >< b)
        return $ a >< b

--セグ木の読み込み
--(left,right)の範囲
readRSegT :: SegT s -> SegT s -> (Int,Int) -> ST s Elem
readRSegT segT lazy (left,right) = do
  bnds <- getBounds segT
  sub segT lazy (fst bnds, (1+(snd bnds))`div`2) 1
  where
    sub :: SegT s -> SegT s -> (Int,Int) -> Int -> ST s Elem
    sub segT' lazy' (l,r) i
      | r < left || right < l = return identity
      | left <= l && r <= right = do
        a <- readArray segT' i
        lanum <- readArray lazy' i
        traceShowM (i,lanum)
        when (lanum /= 0) $ do
          readArray segT' i >>= \a -> writeArray segT' i (nthfunc lanum a)
          writeArray lazy' i 0
        return $ nthfunc lanum a
      | otherwise  = do
        let mid = (l+r)`div`2
            tochild = id --(`div`2)
        lanum <- readArray lazy' i
        traceShowM (i,lanum)
        when (lanum /= 0) $ do
          readArray segT' i >>= \a -> writeArray segT' i (nthfunc lanum a)
          writeArray lazy' (2*i)   (tochild lanum)
          writeArray lazy' (2*i+1) (tochild lanum)
          writeArray lazy' i 0
        vr <- sub segT' lazy' (mid+1,r) (2*i+1)
        vl <- sub segT' lazy' (l,mid) (2*i)
        return $ vr >< vl
