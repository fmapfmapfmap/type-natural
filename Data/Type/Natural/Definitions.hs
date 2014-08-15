{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude   #-}
{-# LANGUAGE PolyKinds, RankNTypes, TemplateHaskell, TypeFamilies, ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, StandaloneDeriving    #-}
module Data.Type.Natural.Definitions where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
import           Data.Singletons.TH       (promote, singletons)
import           Data.Promotion.TH        (promoteOrdInstances)
import           Data.Singletons.Prelude
import           Data.Singletons.Decide
import qualified Data.Singletons.TypeLits as TL
#else
import           Data.Singletons
#endif
import           Prelude
import qualified Prelude                  as P
import           Unsafe.Coerce
import Proof.Equational ((:=:))
import Proof.Equational (coerce)

--------------------------------------------------
-- * Natural numbers and its singleton type
--------------------------------------------------
singletons [d|
 data Nat = Z | S Nat
            deriving (Show, Eq)
 |]

deriving instance Show (SNat n)

instance Eq (SNat n) where
  _ == _ = True
  _ /= _ = False

--------------------------------------------------
-- ** Arithmetic functions.
--------------------------------------------------

instance Ord Nat where
  {-
  compare Z Z = EQ
  compare Z (S _) = LT
  compare (S _) Z = GT
  compare (S n) (S m) = compare n m
-}
  Z    <= _ = True
  S _ <= Z = False
  S n <= S m = n <= m

-- | Boolean-valued type-level comparison function.
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
promoteOrdInstances [''Nat]

succLeqEq :: SNat n -> SNat m -> (n :<= m) :=: (S n :<= S m)
succLeqEq _ _ = unsafeCoerce (Refl :: () :=: ())
-- The following is proof of the validness:
{- 
succLeqEq :: SNat n -> SNat m -> (n :<= m) :=: (S n :<= S m)
succLeqEq n m =
  case sCompare n m of
    SLT -> Refl
    SGT -> Refl
    SEQ -> Refl
-}

instance SOrd ('KProxy :: KProxy Nat) where
  sCompare SZ SZ = SEQ
  sCompare SZ (SS _) = SLT
  sCompare (SS _) SZ = SGT
  sCompare (SS n) (SS m) = sCompare n m
  SZ   %:<= SZ   = STrue
  SZ   %:<= SS _ = STrue
  SS _ %:<= SZ   = SFalse
  SS n %:<= SS m = coerce (succLeqEq n m) $ n %:<= m 
  n %:<  m = case sCompare n m of { SLT -> STrue ; SEQ -> SFalse ; SGT -> SFalse }
  n %:>= m = case sCompare n m of { SLT -> SFalse ; SEQ -> STrue ; SGT -> STrue }
  n %:>  m = case sCompare n m of { SLT -> SFalse ; SEQ -> SFalse ; SGT -> STrue }
  sMin n m = unsafeCoerce $ sIf (n %:<= m) n m
  sMax m n = unsafeCoerce $ sIf (n %:<= m) m n -- Why do I need these @unsafeCoerce@s?
#else
singletons [d|
 -- | Minimum function.
 min :: Nat -> Nat -> Nat
 min Z     Z     = Z
 min Z     (S _) = Z
 min (S _) Z     = Z
 min (S m) (S n) = S (min m n)

 -- | Maximum function.
 max :: Nat -> Nat -> Nat
 max Z     Z     = Z
 max Z     (S n) = S n
 max (S n) Z     = S n
 max (S n) (S m) = S (max n m)
 |]
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
promote [d|
 instance Num Nat where
   Z   + n = n
   S m + n = S (m + n)

   n   - Z   = n
   S n - S m = n - m
   Z   - S _ = Z

   Z   * _ = Z
   S n * m = n * m + m

   negate _ = error "natural cannot negate"
   fromInteger 0 = Z
   fromInteger n = S (P.fromInteger (n P.- 1))

   abs n = n
   signum Z = Z
   signum _ = S Z
 |]

sfromint :: TL.SNat n -> SNat (FromInteger n)
sfromint n =
  case n %~ pzero of
    Proved Refl -> SZ
    Disproved _ -> unsafeCoerce $ SS $ sFromInteger (n %:- pone)
  where
    pone  = TL.SNat :: TL.SNat 1
    pzero = TL.SNat :: TL.SNat 0

instance SNum ('KProxy :: KProxy Nat) where
   SZ   %:+ n = n
   SS m %:+ n = SS (m %:+ n)

   n    %:- SZ   = n
   SS n %:- SS m = n %:- m
   SZ   %:- SS _ = SZ

   SZ   %:* _ = SZ
   SS n %:* m = n %:* m %:+ m

   sNegate _ = sError (TL.SSym :: TL.SSymbol "natural cannot negate")

   sAbs n = n
   sSignum SZ = SZ
   sSignum (SS _) = SS SZ

   sFromInteger = sfromint
#else
singletonsOnly [d|
 (+) :: Nat -> Nat -> Nat
 Z   + n = n
 S m + n = S (m + n)

 (-) :: Nat -> Nat -> Nat
 n   - Z   = n
 S n - S m = n - m
 Z   - S _ = Z

 (*) :: Nat -> Nat -> Nat
 Z   * _ = Z
 S n * m = n * m + m
 |]
#endif
infixl 6 :-:

type n :-: m = n :- m
infixl 6 :+:, %+

type n :+: m = n :+ m

-- | Addition for singleton numbers.
(%+) :: SNat n -> SNat m -> SNat (n :+: m)
(%+) = (%:+)

infixl 7 :*:, %*

-- | Type-level multiplication.
type n :*: m = n :* m

-- | Multiplication for singleton numbers.
(%*) :: SNat n -> SNat m -> SNat (n :*: m)
(%*) = (%:*)

singletons [d|
 zero, one, two, three, four, five, six, seven, eight, nine, ten :: Nat           
 eleven, twelve, thirteen, fourteen, fifteen, sixteen, seventeen, eighteen, nineteen, twenty :: Nat           
 zero      = Z
 one       = S zero
 two       = S one
 three     = S two
 four      = S three
 five      = S four
 six       = S five
 seven     = S six
 eight     = S seven
 nine      = S eight
 ten       = S nine
 eleven    = S ten
 twelve    = S eleven
 thirteen  = S twelve
 fourteen  = S thirteen
 fifteen   = S fourteen
 sixteen   = S fifteen
 seventeen = S sixteen
 eighteen  = S seventeen
 nineteen  = S eighteen
 twenty    = S nineteen
 n0, n1, n2, n3, n4, n5, n6, n7, n8, n9 :: Nat
 n10, n11, n12, n13, n14, n15, n16, n17 :: Nat
 n18, n19, n20 :: Nat
 n0  = zero
 n1  = one
 n2  = two
 n3  = three
 n4  = four
 n5  = five
 n6  = six
 n7  = seven
 n8  = eight
 n9  = nine
 n10 = ten
 n11 = eleven
 n12 = twelve
 n13 = thirteen
 n14 = fourteen
 n15 = fifteen
 n16 = sixteen
 n17 = seventeen
 n18 = eighteen
 n19 = nineteen
 n20 = twenty
 |]

