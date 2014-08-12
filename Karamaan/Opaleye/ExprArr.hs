{-# LANGUAGE
    DeriveFunctor
  , FlexibleContexts
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}
module Karamaan.Opaleye.ExprArr
    ( Scope
    , ExprArr
    , Expr
    , CaseArg
    , CaseRunner
    , runExprArr''
    , scopeOfWire
    , scopeOfCols
    , runExprArrStartEmpty
    , runExprArrStart
    , emptyScope
    , unsafeScopeLookup
    , unsafeCoerce
    , scopeUnion
    , eq
    , plus
    , mul
    , constant
    , constantRC
    , or
    , toQueryArr
    , toQueryArrDef
    , and
    , not
    , constantLit
    , constantDay
    , equalsOneOf
    , cat
    , notEq
    , unOp
    , lt
    , lte
    , gt
    , gte
    , mod
    , abs
    , divide
    , times
    , minus
    , signum
    , case_
    , runCase
    , ifThenElse
    , caseMassage
    , cast
    , lower
    , coalesce
    , coalesceText
    ) where

import Control.Applicative (Applicative (..))
import Control.Arrow (Arrow, arr, first, second, (&&&), (***))
import Control.Category (Category, (<<<))
import Data.Map (Map)
import Data.Profunctor (Profunctor, dimap)
import Data.Profunctor.Product (ProductProfunctor, empty, (***!))
import Data.Text (Text)
import Data.Time.Calendar (Day)
import Database.HaskellDB.PrimQuery (Literal, PrimExpr, extend)
import Database.HaskellDB.Query (ShowConstant, showConstant)
import Karamaan.Opaleye.Operators (operatorName)
import Karamaan.Opaleye.QueryArr (QueryArr (QueryArr), Tag, first3, next, start, tagWith)
import Karamaan.Opaleye.Wire (Wire (Wire))
import Karamaan.Plankton.Arrow (foldrArr, opC, replaceWith)
import Prelude hiding (abs, and, mod, not, or, signum)
import qualified Control.Category
import qualified Data.List                       as List
import qualified Data.Map                        as Map
import qualified Data.Profunctor.Product         as P
import qualified Data.Profunctor.Product.Default as D
import qualified Data.Text                       as T
import qualified Database.HaskellDB.PrimQuery    as PQ
import qualified Karamaan.Opaleye.Unpackspec     as U
import qualified Karamaan.Opaleye.Values         as Values
import qualified Karamaan.Opaleye.Wire           as Wire
import qualified Prelude

-- This is a more type-safe way, and a nicer API, to doing the PrimExpr
-- fiddling that Predicates.hs does.  When there's time we'll convert
-- all of Predicates.hs to this way of doing things.

type Scope = Map String PrimExpr

emptyScope :: Scope
emptyScope = Map.empty

-- An ExprArr takes some wires, a scope to look up the meaning of the
-- wires in (returning a PrimExpr) and a fresh tag.
--
-- It returns the new wires, a scope for looking up the new wires in
-- and a new fresh tag.  The returned scope only has to be so big as
-- to contain the new wires so we are at liberty to throw the old
-- scope away if we like.
newtype ExprArr a b = ExprArr ((a, Scope, Tag) -> (b, Scope, Tag))
  deriving (Functor)

instance Applicative (ExprArr a) where
  pure = arr . const
  f <*> x = arr (uncurry ($)) <<< (f &&& x)

instance (Num b, ShowConstant b) => Num (ExprArr a (Wire b)) where
  f + g    = plus   <<< (f &&& g)
  f - g    = minus  <<< (f &&& g)
  f * g    = mul    <<< (f &&& g)
  abs    f = abs    <<< f
  signum f = signum <<< f
  fromInteger = constantRC . fromInteger

type Expr b = ExprArr () b

instance Category ExprArr where
  id = ExprArr id
  ExprArr g . ExprArr f = ExprArr (g . f)

instance Arrow ExprArr where
  arr f = ExprArr (first3 f)
  first f = ExprArr g
    where g ((a, z), scope, t0) = ((b, z), scope' `Map.union` scope, t1)
            where (b, scope', t1) = runExprArr f (a, scope, t0)

instance Profunctor ExprArr where
  dimap f g a = arr g <<< a <<< arr f

instance ProductProfunctor ExprArr where
  empty = Control.Category.id
  (***!) = (***)

runExprArr :: ExprArr a b -> (a, Scope, Tag) -> (b, Scope, Tag)
runExprArr (ExprArr f) = f

runExprArrStart :: ExprArr a b -> (a, Scope) -> (b, Scope, Tag)
runExprArrStart expr (a, scope) = runExprArr expr (a, scope, start)

runExprArrStartEmpty :: ExprArr a b -> a -> (b, Scope, Tag)
runExprArrStartEmpty expr a = runExprArr expr (a, emptyScope, start)

runExprArr'' :: ExprArr a (Wire b) -> (a, Scope) -> PrimExpr
runExprArr'' expr (a, scope) = unsafeScopeLookup b scope1
  where (b, scope1, _) = runExprArrStart expr (a, scope)

-- Note that we only need to be able to look up the returned Wire in
-- the returned Scope, so it's not a mistake to ignore the argument
-- Scope.
constantLit :: Literal -> Expr (Wire a)
constantLit l = ExprArr g
  where g ((), _, t0) = (w, scope, next t0)
          where ws = tagWith t0 "constant"
                w = Wire ws
                scope = Map.singleton ws (PQ.ConstExpr l)

{-| 'constant' should be considered deprecated.
    Use Karamaan.Opaleye.ShowConstant.showConstant instead
-}
constant :: ShowConstant a => a -> Expr (Wire a)
constant = constantLit . showConstant

constantRC :: ShowConstant a => a -> ExprArr b (Wire a)
constantRC = replaceWith . constant

-- Probably best just to use Karamaan.Opaleye.ShowConstant.showConstant
-- these days.  constantDay will be deprecated at some point in the future.
constantDay :: Day -> Expr (Wire Day)
constantDay = unsafeConstant . Values.dayToSQL

unsafeConstant :: String -> Expr (Wire a)
unsafeConstant = constantLit . PQ.OtherLit

unsafeCoerce :: ExprArr (Wire a) (Wire b)
unsafeCoerce = arr Wire.unsafeCoerce

-- TODO: ExprArr (Wire a, Wire b) (Wire c)?
binOp :: PQ.BinOp -> String -> ExprArr (Wire a, Wire a) (Wire b)
binOp op name = makeExprArr wireName primExpr
  where wireName u = operatorName v name v'
          where (Wire v, Wire v') = u
        primExpr lookupS (Wire u, Wire u') = PQ.BinExpr op uExpr u'Expr
          where uExpr = lookupS u
                u'Expr = lookupS u'

-- Generically make an operation of one argument
unG :: (op -> arg -> PrimExpr) -> (PrimExpr -> arg) -> op -> [Char]
       -> ExprArr (Wire a) (Wire b)
unG expr wrap op name = makeExprArr wireName primExpr
  where wireName u = name ++ "_" ++ take 5 v
          where Wire v = u
        primExpr lookupS (Wire u) = expr op (wrap uExpr)
          where uExpr = lookupS u

unOp :: PQ.UnOp -> String -> ExprArr (Wire a) (Wire b)
unOp = unG PQ.UnExpr id

unFun :: String -> String -> ExprArr (Wire a) (Wire b)
unFun = unG PQ.FunExpr (\x -> [x])

makeExprArr :: (wires -> String) -> ((String -> PrimExpr) -> wires -> PrimExpr)
               -> ExprArr wires (Wire a)
makeExprArr wireName primExpr = ExprArr g where
  g (u, scope, t0) = (w, scope', next t0)
    where ws = tagWith t0 (wireName u)
          w = Wire ws
          lookupS = flip unsafeScopeLookup' scope
          scope' = Map.singleton ws (primExpr lookupS u)

abs :: ExprArr (Wire a) (Wire a)
abs = unOp (PQ.UnOpOther "@") "abs"

signum :: ExprArr (Wire a) (Wire a)
signum = unFun "sign" "sign"

plus :: ExprArr (Wire a, Wire a) (Wire a)
plus = binOp PQ.OpPlus "plus"

minus :: ExprArr (Wire a, Wire a) (Wire a)
minus = binOp PQ.OpMinus "minus"

-- TODO: deprecate this one
mul :: ExprArr (Wire a, Wire a) (Wire a)
mul = binOp PQ.OpMul "mul"

times :: ExprArr (Wire a, Wire a) (Wire a)
times = binOp PQ.OpMul "times"

divide :: ExprArr (Wire a, Wire a) (Wire a)
divide = binOp PQ.OpDiv "div"

-- HaskellDB's OpMod comes out as "x MOD y" which Postgres doesn't like
-- TODO: the solution to this is to make sure we use the correct SQL
-- generator.  See
-- http://hackage.haskell.org/packages/archive/haskelldb/2.2.2/doc/html/src/Database-HaskellDB-Sql-PostgreSQL.html#generator
mod :: ExprArr (Wire a, Wire a) (Wire a)
mod = binOp (PQ.OpOther "%") "mod"

gt :: ExprArr (Wire a, Wire a) (Wire Bool)
gt = binOp PQ.OpGt "gt"

gte :: ExprArr (Wire a, Wire a) (Wire Bool)
gte = binOp PQ.OpGtEq "gte"

lt :: ExprArr (Wire a, Wire a) (Wire Bool)
lt = binOp PQ.OpLt "lt"

lte :: ExprArr (Wire a, Wire a) (Wire Bool)
lte = binOp PQ.OpLtEq "lte"

or :: ExprArr (Wire Bool, Wire Bool) (Wire Bool)
or = binOp PQ.OpOr "or"

and :: ExprArr (Wire Bool, Wire Bool) (Wire Bool)
and = binOp PQ.OpAnd "and"

not :: ExprArr (Wire Bool) (Wire Bool)
not = unOp PQ.OpNot "not"

eq :: ExprArr (Wire a, Wire a) (Wire Bool)
eq = binOp PQ.OpEq "eq"

notEq :: ExprArr (Wire a, Wire a) (Wire Bool)
notEq = binOp PQ.OpNotEq "noteq"

cat :: ExprArr (Wire String, Wire String) (Wire String)
cat = binOp (PQ.OpOther "||") "cat"

equalsOneOf :: ShowConstant a => [a] -> ExprArr (Wire a) (Wire Bool)
-- TODO: Should this be foldl', since laziness gets us nothing here?
equalsOneOf = foldrArr or false . map (opC eq . constant)
  where false = replaceWith (constant False)

-- Case

type CaseArg a = ([(Wire Bool, a)], a)

fmapCaseArg :: (a -> b) -> CaseArg a -> CaseArg b
fmapCaseArg f = map (second f) *** f

newtype CaseRunner a b = CaseRunner (ExprArr (CaseArg a) b)

instance Profunctor CaseRunner where
  dimap f g (CaseRunner q) = CaseRunner (dimap (fmapCaseArg f) g q)

instance Functor (CaseRunner a) where
  fmap f (CaseRunner c) = CaseRunner (fmap f c)

instance Applicative (CaseRunner a) where
  pure = CaseRunner . pure
  CaseRunner f <*> CaseRunner x = CaseRunner (f <*> x)

instance ProductProfunctor CaseRunner where
  empty = P.defaultEmpty
  (***!) = P.defaultProfunctorProduct

instance D.Default CaseRunner (Wire a) (Wire a) where
  def = CaseRunner caseWire

runCase :: CaseRunner a b -> ExprArr (CaseArg a) b
runCase (CaseRunner q) = q

case_ :: D.Default CaseRunner a a => ExprArr (CaseArg a) a
case_ = runCase D.def

caseWire :: ExprArr (CaseArg (Wire a)) (Wire a)
caseWire = makeExprArr wireName primExpr
  where wireName _ = "case_result"
        primExpr lookupS (cases, Wire else_) = PQ.CaseExpr casesP elseP
          where elseP = lookupS else_
                casesP = map condWires cases
                condWires (Wire cond, Wire result)
                  = (lookupS cond, lookupS result)

ifThenElse :: D.Default CaseRunner a a
              => ExprArr (Wire Bool, a, a) a
ifThenElse = case_ <<< arr caseMassage

caseMassage :: (Wire Bool, a, a) -> ([(Wire Bool, a)], a)
caseMassage (cond, ifTrue, ifFalse) = ([(cond, ifTrue)], ifFalse)

-- Converting ExprArrs to QueryArrs

toQueryArr :: U.Unpackspec a -> U.Unpackspec b -> ExprArr a b -> QueryArr a b
toQueryArr writera writerb exprArr = QueryArr f
  where f (w0, primQ0, t0) = (w1, primQ1, t1)
          where scope0 = scopeOfCols writera w0
                (w1, scope1, t1) = runExprArr exprArr (w0, scope0, t0)
                exprs = (map (\w -> (w, unsafeScopeLookup' w scope1))
                         . U.runUnpackspec writerb) w1
                primQ1 = extend exprs primQ0

scopeUnion :: [Scope] -> Scope
scopeUnion = scopeUnion' where
  scopeUnion' :: Ord k => [Map k v] -> Map k v
  scopeUnion' = List.foldl' Map.union Map.empty

toQueryArrDef :: (D.Default (P.PPOfContravariant U.Unpackspec) a a,
                  D.Default (P.PPOfContravariant U.Unpackspec) b b)
                 => ExprArr a b -> QueryArr a b
toQueryArrDef = toQueryArr (P.unPPOfContravariant D.def)
                           (P.unPPOfContravariant D.def)

scopeOfWire :: Wire a -> Scope
scopeOfWire (Wire s) = Map.singleton s (PQ.AttrExpr s)

scopeOfCols :: U.Unpackspec wires -> wires -> Scope
scopeOfCols unpackspec = scopeUnion
                         . map (scopeOfWire . Wire)
                         . U.runUnpackspec unpackspec

unsafeScopeLookup :: Wire a -> Scope -> PrimExpr
unsafeScopeLookup (Wire w) = unsafeScopeLookup' w

unsafeScopeLookup' :: String -> Scope -> PrimExpr
unsafeScopeLookup' w s = case Map.lookup w s of
  Nothing -> error ("Could not find Wire " ++ w ++ " in scope")
  Just a  -> a

lower :: ExprArr (Wire Text) (Wire Text)
lower = unFun "lower" "lower"

-- TODO unsafe
-- TODO Accepts multiple columns
coalesce :: ShowConstant s => s -> ExprArr (Wire (Maybe a)) (Wire a)
coalesce lit = makeExprArr wireName primExpr
  where wireName u = "coalesce_" ++ take 5 v
          where Wire v = u
        primExpr lookupS (Wire u) = PQ.FunExpr "coalesce" [uExpr, PQ.ConstExpr (showConstant lit)]
          where uExpr = lookupS u

coalesceText :: Text -> ExprArr (Wire (Maybe Text)) (Wire Text)
coalesceText = coalesce . T.unpack

-- TODO unsafe
cast :: String -> ExprArr (Wire a) (Wire b)
cast ty = makeExprArr wireName primExpr
  where wireName u = "cast_" ++ take 5 v
          where Wire v = u
        primExpr lookupS (Wire u) = PQ.CastExpr ty uExpr
          where uExpr = lookupS u
