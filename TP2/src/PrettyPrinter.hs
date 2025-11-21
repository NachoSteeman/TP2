module PrettyPrinter
  ( printTerm  ,     -- pretty printer para terminos
    printType        -- pretty printer para tipos
  )
where

import  Common
import  Text.PrettyPrint.HughesPJ
import  Prelude hiding ((<>))

-- lista de posibles nombres para variables
vars :: [String]
vars =
  [ c : n
  | n <- "" : map show [(1 :: Integer) ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- pretty-printer de términos

pp :: Int -> [String] -> Term -> Doc
pp ii vs (Bound k         ) = text (vs !! (ii - k - 1))
pp _  _  (Free  (Global s)) = text s

pp ii vs (i :@: c         ) = sep
  [ parensIf (isLam i) (pp ii vs i)
  , nest 1 (parensIf (isLam c || isApp c) (pp ii vs c))
  ]

pp ii vs (Lam t c) =
  text "\\"
    <> text (vs !! ii)
    <> text ":"
    <> printType t
    <> text ". "
    <> pp (ii + 1) vs c

-- Let:
pp ii vs (Let t1 t2)      =  
  text "let" 
    <> text (vs !! ii) 
    <> text " = "
    <> pp ii vs t1
    <> text "in"
    <> pp (ii + 1) vs t2 

-- Nat:
pp ii vs Zero             = text $ show (sucToNat Zero)
pp ii vs n@(Suc t1)       = text $ show (sucToNat n)
pp ii vs (Rec t1 t2 t3)   = 
  text "Rec"
  <> pp ii vs t1
  <> pp ii vs t2
  <> pp ii vs t3

-- List:
pp ii vs Nil              = text "Nil"
pp ii vs (Cons t1 t2)     = 
  text "Cons"
  <> pp ii vs t1
  <> pp ii vs t2

pp ii vs (RecL t1 t2 t3)  = 
  text "RL"
  <> pp ii vs t1
  <> pp ii vs t2
  <> pp ii vs t3 




sucToNat :: Term -> Int
sucToNat Zero    = 0
sucToNat (Suc n) = 1 + sucToNat n

isLam :: Term -> Bool
isLam (Lam _ _) = True
isLam _         = False

isApp :: Term -> Bool
isApp (_ :@: _) = True
isApp _         = False

-- pretty-printer de tipos
printType :: Type -> Doc
printType EmptyT       = text "E"
printType NatT         = text "Nat"
printType ListT        = text "List Nat"
printType (FunT t1 t2) =
  sep [parensIf (isFun t1) (printType t1), text "->", printType t2]


isFun :: Type -> Bool
isFun (FunT _ _) = True
isFun _          = False

fv :: Term -> [String]
fv (Bound _         ) = []
fv (Free  (Global n)) = [n]
fv (t   :@: u       ) = fv t ++ fv u
fv (Lam _   u       ) = fv u
fv (Let t1 t2       ) = fv t1 ++ fv t2 
fv Zero               = []
fv (Suc t)            = fv t
fv (Rec t1 t2 t3)     = fv t1 ++ fv t2 ++ fv t3
fv Nil                = []
fv (Cons t1 t2)       = fv t1 ++ fv t2
fv (RecL t1 t2 t3)    = fv t1 ++ fv t2 ++ fv t3

---
printTerm :: Term -> Doc
printTerm t = pp 0 (filter (\v -> not $ elem v (fv t)) vars) t
