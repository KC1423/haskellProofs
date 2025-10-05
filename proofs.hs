{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Type.Equality
import Data.Kind

data Nat = Z | S Nat

--data a :~: b where
--  Refl :: a :~: a

type family a + b where
  a + Z = a
  a + S b = S (a + b)

type family a :*: b where
  a :*: Z = Z
  a :*: S b = (a :*: b) + a

testEquality :: (Z + Z) :~: Z
testEquality = Refl

testEquality' :: (a + Z) :~: a
testEquality' = Refl

testEquality'' :: (a + S b) :~: S (a + b)
testEquality'' = Refl

testEquality''' :: (a :*: Z) :~: Z
testEquality''' = Refl

testEquality'''' :: (a :*: S b) :~: ((a :*: b) + a)
testEquality'''' = Refl

data SNat :: Nat -> * where
  SZ :: SNat Z
  SS :: SNat a -> SNat (S a)

plusLeftId :: SNat a -> (Z + a) :~: a
plusLeftId SZ = Refl
plusLeftId (SS n) = gcastWith (plusLeftId n) Refl

given1 :: SNat a -> (a + Z) :~: a
given1 _ = Refl

given2 :: SNat a -> SNat b -> (a + S b) :~: S (a + b)
given2 _ _ = Refl

plusRightId :: SNat a -> (a + Z) :~: a
plusRightId = given1

-- proof of (a + b) + c = a + (b + c)
(!+) :: SNat n -> SNat m -> SNat (n + m)
n !+ SZ = n
n !+ (SS m) = SS (n !+ m)

(!*) :: SNat n -> SNat m -> SNat (n :*: m)
n !* SZ = SZ
n !* (SS m) = (n !* m) !+ n

-- transitivity :: a=b and b=c -> a=c
(==>) :: (a :~: b) -> (b :~: c) -> (a :~: c)
Refl ==> Refl = Refl

{-plusAssoc
  :: SNat a
  -> SNat b
  -> SNat c
  -> ((a + b) + c) :~: (a + (b + c))
plusAssoc a b SZ =
  let
    step1 :: SNat x -> SNat y -> ((x + y) + Z) :~: (x + y)
    step1 x y = gcastWith (given1 (x !+ y)) Refl -- (1)

    step2 :: SNat x -> SNat y -> (x + y) :~: (x + (y + Z))
    step2 x y = gcastWith (given1 y) Refl -- (1)
  in (step1 a b) ==> (step2 a b)
plusAssoc a b (SS c) =
  let
    step1
      :: SNat x -> SNat y -> SNat (S z) -> ((x + y) + S z) :~: S ((x + y) + z)
    step1 x y (SS z) = gcastWith (given2 (x !+ y) (SS z)) Refl -- (2)

    step2
      :: SNat x -> SNat y -> SNat z -> S ((x + y) + z) :~: S (x + (y + z))
    step2 x y z = gcastWith (plusAssoc x y z) Refl -- induction

    step3
      :: SNat x -> SNat y -> SNat z -> S (x + (y + z)) :~: (x + S (y + z))
    step3 x y z = gcastWith (given2 x (y !+ z)) Refl -- (2)

    step4
      :: SNat x -> SNat y -> SNat z -> (x + S (y + z)) :~: (x + (y + S z))
    step4 x y z = gcastWith (given2 y z) Refl -- (2)
  in step1 a b (SS c) ==> step2 a b c ==> step3 a b c ==> step4 a b c-}
plusAssoc :: SNat a -> SNat b -> SNat c -> ((a + b) + c) :~: (a + (b + c))
plusAssoc a b SZ = Refl
plusAssoc a b (SS c) = gcastWith (plusAssoc a b c) Refl

{-
let b = S n, assume a + n = n + a
a + S n
 = a + (n + 1)
 =  (a + n) + 1
 = 1 + (a + n)
 = 1 + (n + a)
 = (1 + n) + a
 = (n + 1) + a
 = S n + a
-}
plusComm :: SNat a -> SNat b -> (a + b) :~: (b + a)
plusComm a SZ = gcastWith (plusLeftId a) Refl
plusComm SZ (SS SZ) = Refl
plusComm (SS n) (SS SZ) = gcastWith (plusComm n (SS SZ)) Refl
plusComm a (SS b) =
  let 
    step1 :: SNat x -> SNat (S y) -> (x + (S y) :~: x + (y + S Z))
    step1 x (SS y) = gcastWith (given2 y (SS SZ)) Refl
    step2 :: SNat x -> SNat y -> (x + (y + S Z) :~: (x + y) + S Z)
    step2 x y = gcastWith (plusAssoc x y (SS SZ)) Refl
    step3 :: SNat x -> SNat y -> ((x + y) + S Z :~: S Z + (x + y))
    step3 x y = gcastWith (plusComm (x !+ y) (SS SZ)) Refl
    step4 :: SNat x -> SNat y -> (S Z + (x + y) :~: S Z + (y + x))
    step4 x y = gcastWith (plusComm x y) Refl
    step5 :: SNat x -> SNat y -> (S Z + (y + x) :~: (S Z + y) + x)
    step5 x y = gcastWith (plusAssoc (SS SZ) y x) Refl
    step6 :: SNat x -> SNat y -> ((S Z + y) + x :~: (y + S Z) + x)
    step6 x y = gcastWith (plusComm (SS SZ) y) Refl
    step7 :: SNat x -> SNat y -> ((y + S Z) + x :~: S y + x)
    step7 x y = gcastWith (given2 y (SS SZ)) Refl
  in step1 a (SS b) ==> step2 a b ==> step3 a b ==> step4 a b ==> 
     step5 a b ==> step6 a b ==> step7 a b

data Tree = Leaf Nat | Branch Nat Tree Tree

type family (FlipTree a) where
  FlipTree (Leaf n) = Leaf n
  FlipTree (Branch n l r) = Branch n (FlipTree r) (FlipTree l)

data STree :: Tree -> * where
  SLeaf :: SNat x -> STree (Leaf x) 
  SBranch :: SNat x -> STree l -> STree r -> STree (Branch x l r)

fgiven1 :: STree (Leaf x) -> FlipTree (Leaf x) :~: Leaf x
fgiven1 _ = Refl

fgiven2 :: STree (Branch x l r) -> 
           FlipTree (Branch x l r) :~: Branch x (FlipTree r) (FlipTree l)
fgiven2 _ = Refl

symFlip :: STree x -> x :~: FlipTree (FlipTree x)
symFlip (SLeaf _) = Refl
symFlip t@(SBranch x l r) =
  let
    step1 :: STree (Branch x l r) -> 
             Branch x l r :~: Branch x (FlipTree (FlipTree l)) r
    step1 (SBranch v lt rt) = gcastWith (symFlip lt) Refl
    step2 :: STree (Branch x l r) ->
             Branch x (FlipTree (FlipTree l)) r :~: 
             Branch x (FlipTree (FlipTree l)) (FlipTree (FlipTree r))
    step2 (SBranch v lt rt) = gcastWith (symFlip rt) Refl
    step3 :: STree (Branch x l r) ->
             Branch x (FlipTree (FlipTree l)) (FlipTree (FlipTree r)) :~:
             FlipTree (Branch x (FlipTree r) (FlipTree l))
    step3 x = gcastWith (fgiven2 x) Refl
    step4 :: STree (Branch x l r) ->
             FlipTree (Branch x (FlipTree r) (FlipTree l)) :~:
             FlipTree (FlipTree (Branch x l r))
    step4 x = gcastWith (fgiven2 x) Refl
  in step1 t ==> step2 t ==> step3 t ==> step4 t

--------------

{-
Take arbitrary x, l, r
Assume l = FlipTree (FlipTree l)
       r = FlipTree (FilipTree r)

Branch x l r
 = Branch x (f (f l)) (f (f r)) by IH
 = f (Branch x (f r) (f l)) by (2)
 = f f (Branch x l r)) by (2)
-}

-- x(y+z) = xy + xz

distrib :: SNat x -> SNat y -> SNat z -> (x + y) :*: z :~: (x :*: z) + (y :*: z)
distrib a b SZ = Refl
distrib a b (SS c) = 
  let
    -- !! Proof step may be omitted if it is just Refl
    --step1 :: SNat x -> SNat y -> SNat (S z) ->
    --         (x + y) :*: S z :~: ((x + y) :*: z) + (x + y)
    step2 :: SNat x -> SNat y -> SNat z ->
             ((x + y) :*: z) + (x + y) :~: ((x :*: z) + (y :*: z)) + (x + y)
    step2 x y z = gcastWith (distrib x y z) Refl
    step3 :: SNat x -> SNat y -> SNat z ->
              ((x :*: z) + (y :*: z)) + (x + y) :~: 
               (x :*: z) + ((y :*: z) + (x + y))
    step3 x y z = gcastWith (plusAssoc (x !* z) (y !* z) (x !+ y)) Refl
    step4 :: SNat x -> SNat y -> SNat z ->
             (x :*: z) + ((y :*: z) + (x + y)) :~: 
             (x :*: z) + ((x + y) + (y :*: z))
    step4 x y z = gcastWith (plusComm (y !* z) (x !+ y)) Refl
    step5 :: SNat x -> SNat y -> SNat z ->
             (x :*: z) + ((x + y) + (y :*: z)) :~:
             (x :*: z) + (x + (y + (y :*: z)))
    step5 x y z = gcastWith (plusAssoc x y (y !* z)) Refl
    step6 :: SNat x -> SNat y -> SNat z ->
             (x :*: z) + (x + (y + (y :*: z))) :~:
             ((x :*: z) + x) + (y + (y :*: z))
    step6 x y z = gcastWith (plusAssoc (x !* z) x (y !+ (y !* z))) Refl
    step7 :: SNat x -> SNat y -> SNat z ->
             ((x :*: z) + x) + (y + (y :*: z)) :~:
             ((x :*: z) + x) + ((y :*: z) + y)
    step7 x y z = gcastWith (plusComm y (y !* z)) Refl
    --step8 :: SNat x -> SNat y -> SNat z ->
    --         ((x :*: z) + x) + ((y :*: z) + y) :~: (x :*: S z) + ((y :*: z) + y)
    --step9 :: SNat x -> SNat y -> SNat z ->
    --         (x :*: S z) + ((y :*: z) + y) :~: (x :*: S z) + (y :*: S z)
  in step2 a b c ==> step3 a b c ==> step4 a b c ==>
     step5 a b c ==> step6 a b c ==> step7 a b c
{-
(x+y)*z = x*z + y*z

Proof by induction over z
Assume (x+y)*z = xz+yz
(x + y) * S z
 = ((x + y) * z) + (x + y)
 = ((x*z) + (y*z)) + (x + y)
 = (x*z) + ((y*z) + (x+y))
 = (x*z) + ((x+y) + (y*z))
 = (x*z) + (x + (y+(y*z)))
 = ((x*z)+x)) + (y+(y*z))
 = ((x*z)+x)) + ((y*z)+y))
 = (x * S z) + (y * S z)
-}

mulRightZero :: SNat x -> (Z :*: x) :~: Z
mulRightZero SZ = Refl
mulRightZero (SS x) = gcastWith (mulRightZero x) Refl

mulRightId :: SNat x -> (S Z :*: x) :~: x
mulRightId SZ = Refl
mulRightId (SS x) = gcastWith (mulRightId x) Refl

mulComm :: SNat x -> SNat y -> (x :*: y) :~: (y :*: x)
mulComm a SZ = gcastWith (mulRightZero a) Refl
mulComm a (SS b) =
  let
    --step1 :: SNat x -> SNat (S y) -> (x :*: S y) :~: (x :*: y) + x
    step2 :: SNat x -> SNat y -> (x :*: y) + x :~: (y :*: x) + x
    step2 x y = gcastWith (mulComm x y) Refl
    step3 :: SNat x -> SNat y -> (y :*: x) + x :~: (y :*: x) + (S Z :*: x)
    step3 x y = gcastWith (mulRightId x) Refl
    step4 :: SNat x -> SNat y -> (y :*: x) + (S Z :*: x) :~: (y + S Z) :*: x
    step4 x y = gcastWith (distrib y (SS SZ) x) Refl
    --step5 :: SNat x -> SNat y -> (y + S Z) :*: x :~: S y :*: x
  in step2 a b ==> step3 a b ==> step4 a b

{-
Prove a * b = b * a by induction
Base: Assume b = 0
a * 0 = 0 * a by right id

Rec: Take S b, assume a * b = b * a
a * S b
 = (a * b) + a
 = (b * a) + a
 = (b * a) + (1 * a)
 = (b + 1) * a
 = S b * a
-}

mulAssoc :: SNat x -> SNat y -> SNat z -> (x :*: y) :*: z :~: x :*: (y :*: z)
mulAssoc a b SZ = Refl
mulAssoc a b (SS c) =
  let
    --step1 :: SNat x -> SNat y -> SNat (S z) ->
    --         (x :*: y) :*: S z :~: ((x :*: y) :*: z) + (x :*: y)
    step2 :: SNat x -> SNat y -> SNat z ->
             ((x :*: y) :*: z) + (x :*: y) :~: (x :*: (y :*: z)) + (x :*: y)
    step2 x y z = gcastWith (mulAssoc x y z) Refl
    step3 :: SNat x -> SNat y -> SNat z ->
             (x :*: (y :*: z)) + (x :*: y) :~: (x :*: y) + (x :*: (y :*: z))
    step3 x y z = gcastWith (plusComm (x !* (y !* z)) (x !* y)) Refl
    step4 :: SNat x -> SNat y -> SNat z ->
             (x :*: y) + (x :*: (y :*: z)) :~: (y :*: x) + (x :*: (y :*: z))
    step4 x y z = gcastWith (mulComm x y) Refl
    step5 :: SNat x -> SNat y -> SNat z ->
             (y :*: x) + (x :*: (y :*: z)) :~: (y :*: x) + ((y :*: z) :*: x)
    step5 x y z = gcastWith (mulComm x (y !* z)) Refl
    step6 :: SNat x -> SNat y -> SNat z ->
             (y :*: x) + ((y :*: z) :*: x) :~: (y + (y :*: z)) :*: x
    step6 x y z = gcastWith (distrib y (y !* z) x) Refl
    step7 :: SNat x -> SNat y -> SNat z ->
             (y + (y :*: z)) :*: x :~: ((y :*: z) + y) :*: x
    step7 x y z = gcastWith (plusComm y (y !* z)) Refl
    --step8 :: SNat x -> SNat y -> SNat z ->
    --         ((y :*: z) + y) :*: x :~: (y :*: S z) :*: x
    step9 :: SNat x -> SNat y -> SNat (S z) ->
             (y :*: S z) :*: x :~: x :*: (y :*: S z)
    step9 x y z = gcastWith (mulComm (y !* z) x) Refl 
  in step2 a b c ==> step3 a b c ==> step4 a b c ==>
     step5 a b c ==> step6 a b c ==> step7 a b c ==> step9 a b (SS c) 

{-
Prove (a * b) * c = a * (b * c)
Base: Take S c, assume (a * b) * c = a * (b * c)
(a * b) * S c
 = ((a * b) * c) + (a * b) by def of *
 = (a * (b * c)) + (a * b) by IH
 = (a * b) + (a * (b * c)) by plusComm
 = (b * a) + (a * (b * c)) by mulComm
 = (b * a) + ((b * c) * a) by mulComm
 = (b + (b * c)) * a by dist
 = ((b * c) + b) * a by plusComm
 = (b * S c) * a by given
 = a * (b * S c) by plusComm
-}

type I = S Z
type II = S I
ii = SS (SS SZ)

addEven :: SNat x -> SNat y -> 
           (x :*: II) + (y :*: II) :~: ((x + y) :*: II)
addEven x y = gcastWith (distrib x y ii) Refl

-- List

data List = Nil | Cons Nat List

data SList :: List -> * where
  SNil :: SList Nil
  SCons :: SNat h -> SList t -> SList (Cons h t)

type family xs :++ ys where
  Nil :++ ys = ys
  (Cons x xs) :++ ys = Cons x (xs :++ ys)

(!++) :: SList xs -> SList ys -> SList (xs :++ ys)
SNil !++ ys = ys
SCons x xs !++ ys = SCons x (xs !++ ys)

type family (Rev xs) where
  Rev Nil = Nil
  Rev (Cons x xs) = (Rev xs) :++ (Cons x Nil) 

srev :: SList xs -> SList (Rev xs)
srev SNil = SNil
srev (SCons x xs) = srev xs !++ (SCons x SNil)

rightNilConcatId :: SList xs -> (xs :++ Nil) :~: xs
rightNilConcatId SNil = Refl
rightNilConcatId (SCons x xs) = gcastWith (rightNilConcatId xs) Refl

concatAssoc :: SList xs -> SList ys -> SList zs 
            -> (xs :++ ys) :++ zs :~: xs :++ (ys :++ zs)
concatAssoc SNil ys zs = Refl 
concatAssoc (SCons x xs) ys zs = gcastWith (concatAssoc xs ys zs) Refl

revLemma :: SList xs -> SList ys -> Rev (xs :++ ys) :~: Rev ys :++ Rev xs
revLemma SNil ys = gcastWith (rightNilConcatId (srev ys)) Refl
revLemma xs@(SCons _ _) ys =
  let 
    --step1 :: SList (Cons a as) -> SList bs
    --      -> Rev ((Cons a as) :++ bs) :~: Rev (Cons a (as :++ bs))
    --step2 :: SList (Cons a as) -> SList bs
    --      -> Rev (Cons a (as :++ bs)) :~: Rev (as :++ bs) :++ Cons a Nil
    step3 :: SList (Cons a as) -> SList bs
          -> Rev (as :++ bs) :++ Cons a Nil :~: (Rev bs :++ Rev as) :++ Cons a Nil
    step3 (SCons a as) bs = gcastWith (revLemma as bs) Refl
    step4 :: SList (Cons a as) -> SList bs
          -> (Rev bs :++ Rev as) :++ Cons a Nil :~: Rev bs :++ (Rev as :++ Cons a Nil)
    step4 (SCons a as) bs = gcastWith (concatAssoc (srev bs) (srev as) (SCons a SNil)) Refl
    --step5 :: SList (Cons a as) -> SList bs
    --      -> Rev bs :++ (Rev as :++ Cons a Nil) :~: Rev bs :++ Rev (Cons a as)
  in step3 xs ys ==> step4 xs ys

revRev :: SList xs -> Rev (Rev xs) :~: xs
revRev SNil = Refl
revRev xs@(SCons _ _) =
  let
    --step1 :: SList (Cons a as) -> Rev (Rev (Cons a as)) :~: Rev (Rev as :++ Cons a Nil)
    step2 :: SList (Cons a as) 
          -> Rev (Rev as :++ Cons a Nil) :~: Rev (Cons a Nil) :++ Rev (Rev as)
    step2 (SCons a as) = gcastWith (revLemma (srev as) (SCons a SNil)) Refl
    step3 :: SList (Cons a as) 
          -> Rev (Cons a Nil) :++ Rev (Rev as) :~: Rev (Cons a Nil) :++ as
    step3 (SCons a as) = gcastWith (revRev as) Refl
    --step4 :: SList (Cons a as) -> Rev (Cons a Nil) :++ as :~: Cons a Nil :++ as
    --step5 :: SList (Cons a as) -> Cons a Nil :++ as :~: Cons a as
  in step2 xs ==> step3 xs

data GenList a = GNil | GCons a (GenList a)

data family Sing (a :: k)

data instance Sing (xs :: GenList a) where
  SGNil :: Sing GNil
  SGCons :: Sing x -> Sing xs -> Sing (GCons x xs)

type family (GenCat xs ys) where
  GenCat GNil ys = ys
  GenCat (GCons x xs) ys = GCons x (GenCat xs ys)

sgcat :: Sing (xs :: GenList a) -> Sing (ys :: GenList a)
      -> Sing (GenCat xs ys :: GenList a)
sgcat SGNil ys = ys
sgcat (SGCons x xs) ys = SGCons x (sgcat xs ys)

type family (GRev xs) where
  GRev GNil = GNil
  GRev (GCons x xs) = GenCat (GRev xs) (GCons x GNil)

sgrev :: Sing (xs :: GenList a) -> Sing (GRev xs :: GenList a)
sgrev SGNil = SGNil
sgrev (SGCons x xs) = sgcat (sgrev xs) (SGCons x SGNil)

gRightNilConcatId :: Sing (xs :: GenList a) -> (GenCat xs GNil) :~: xs
gRightNilConcatId SGNil = Refl
gRightNilConcatId (SGCons x xs) = gcastWith (gRightNilConcatId xs) Refl

gConcatAssoc :: Sing (xs :: GenList a) 
             -> Sing (ys :: GenList a) 
             -> Sing (zs :: GenList a) 
             -> GenCat (GenCat xs ys) zs :~: GenCat xs (GenCat ys zs)
gConcatAssoc SGNil ys zs = Refl 
gConcatAssoc (SGCons x xs) ys zs = gcastWith (gConcatAssoc xs ys zs) Refl

gRevLemma :: Sing (xs :: GenList a) 
          -> Sing (ys :: GenList a)
          -> GRev (GenCat xs ys) :~: GenCat (GRev ys) (GRev xs)
gRevLemma SGNil ys = gcastWith (gRightNilConcatId (sgrev ys)) Refl
gRevLemma xs@(SGCons _ _) ys =
  let 
    step3 :: Sing (GCons a as :: GenList k)
          -> Sing (bs :: GenList k)
          -> GenCat (GRev (GenCat as bs)) (GCons a GNil) :~: GenCat (GenCat (GRev bs) (GRev as)) (GCons a GNil)
    step3 (SGCons a as) bs = gcastWith (gRevLemma as bs) Refl
    step4 :: Sing (GCons a as :: GenList k) -> Sing (bs :: GenList k)
          -> GenCat (GenCat (GRev bs) (GRev as)) (GCons a GNil) :~: GenCat (GRev bs) (GenCat (GRev as) (GCons a GNil))
    step4 (SGCons a as) bs = gcastWith (gConcatAssoc (sgrev bs) (sgrev as) (SGCons a SGNil)) Refl
  in step3 xs ys ==> step4 xs ys

gRevRev :: Sing (xs :: GenList a) -> GRev (GRev xs) :~: xs
gRevRev SGNil = Refl
gRevRev xs@(SGCons _ _) =
  let
    step2 :: Sing (GCons a as :: GenList k) 
          -> GRev (GenCat (GRev as) (GCons a GNil)) :~: GenCat (GRev (GCons a GNil)) (GRev (GRev as))
    step2 (SGCons a as) = gcastWith (gRevLemma (sgrev as) (SGCons a SGNil)) Refl
    step3 :: Sing (GCons a as :: GenList k) 
          -> GenCat (GRev (GCons a GNil)) (GRev (GRev as)) :~: GenCat (GRev (GCons a GNil)) as
    step3 (SGCons a as) = gcastWith (gRevRev as) Refl
  in step2 xs ==> step3 xs



{-
data SList :: List -> * where
  SNil :: SList Nil
  SCons :: SNat h -> SList t -> SList (Cons h t)
-}


{-

General formula for creating a proof in Haskell:
 1. Define your types properly
 2. Define singleton types for those types
 3. Define type families for your functions
 4. Define singleton analogues for those functions
 5. Create a type signature representing your proof
 6. Map each individual step out in type signature form
 7. Define each step
 8. Join each step in the end with ==>
 9. Optional: where the proof is just Refl or gcastWith Refl Refl etc., the step may be omitted

-}
