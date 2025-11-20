module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-----------------------
-- conversion
-----------------------



-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion (LVar x)         =  (Free (Global x))
conversion (LAbs idx t m)  =  let term' = conversion m 
                              in Lam t  (b2b (Global idx) 0 term') -- Lo casteo a Global a idx para que no tener error de tipos en b2b
conversion (LApp m n)       =  (conversion m) :@: (conversion n)

-- Seccion 8:
conversion (LLet string m n) = Let (conversion m) (conversion n)

-- Naturales:
conversion (LZero)      = Zero
conversion (LSuc n)     = Suc (conversion n)
conversion (LRec n m p) = Rec (conversion n) (conversion m) (conversion p) 

-- Listas:
conversion (LNil)       = Nil 
conversion (LCons n m)  = Cons (conversion n) (conversion m)











-- b2b: Convierte de Brujin a Bound ?????????? VER
b2b :: Name -> Int -> Term -> Term
b2b idx i (Bound n)       = (Bound n)
b2b idx i (Free name)     = if (idx == name) then (Bound i) else (Free name)
b2b idx i (t1 :@: t2)     = (b2b idx i t1) :@: (b2b idx i t2)
b2b idx i (Lam t term) = Lam t (b2b idx (i+1) term)

b2b idx i (Let t1 t2)     = Let (b2b idx i t1) (b2b idx (i+1) t2)

b2b idx i Zero            = Zero
b2b idx i (Suc n)         = Suc (b2b idx i n)
b2b idx i (Rec n m p)     = Rec (b2b idx i n) (b2b idx i m) (b2b idx i p)
b2b idx i Nil             = Nil
b2b idx i (Cons n m)      = Cons (b2b idx i n) (b2b idx i m)

----------------------------
--- evaluador de términos
----------------------------


-- substituye una variable por un término en otro término
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)

-- convierte un valor en el término equivalente
quote :: Value -> Term
quote (VLam t f) = Lam t f

quote (VNum NZero) = Zero
quote (VNum (NSuc n)) = Suc (quote (VNum n))

quote VNil = Nil
quote (VCons n xs) = Cons (quote (VNum n)) (quote (VList xs))











-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval e (Bound i) = error ("Variable ligada fuera de alcance: " ++ show i)
eval e (Free name )    = case lookup name e of
                            Just (v, _) -> v
                            Nothing     -> error ("Variable no definida: " ++ show name)
eval e (Lam t term)    = VLam t term                                        
eval e (t :@: u)     = let  (VLam _ body) = eval e t 
                       in   eval e (sub 0 (quote (eval e u)) body)

-- Seccion 8:
eval e (Let t1 t2) = let v = eval e t1
                     in (sub 0 (quote v) t2) 

-- Seccion Nat
eval e Zero      = VNum NZero
eval e (Suc t)   = case eval e t of
                     VNum n -> VNum (NSuc n)
                     _      -> error "Suc aplicado a no-numero"

-- Seccion List:
eval e Nil         = VList VNil
eval e (Cons t u)  = VList (VCons (eval e t) (eval e u))








----------------------
--- type checker
-----------------------

-- infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=) :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type

-- Reglas de tipado Basicas: 
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t

infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt

infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu

-- Reglas de tipado para Let:
infer' c e (Let term1 term2) =  infer' c e term1 >>= \t1 -> 
                                infer' (t1:c) e term2 

-- Reglas de tipado para Nat:
infer' _ _ Zero    = ret NatT

infer' c e (Suc t) = infer' c e t >>= \tType ->
            case tType of 
              NatT -> ret NatT
              errType    -> notfunError errType


infer' c e (Rec t1 t2 t3) = do t1Type <- infer' c e t1
                               t2Type <- infer' c e t2
                               t3Type <- infer' c e t3
                            case t3Type of
                              NatT ->  case t2Type of
                                          FunT t1Type' (FunT NatT t1Type'') -> if t1Type' == t1Type 
                                                                                    then  if t1Type == t1Type''
                                                                                             then ret t1Type
                                                                                             else matchError t1Type t1Type''
                                                                                  else matchError t1Type t1Type'
                                          _ -> notfunError t2Type
                              
                            
                              _    -> matchError NatT t3Type 
                               

-- Reglas de tipado para Listas:
infer' c e Nil          = ret ListT
infer' c e (Cons t1 t2) = do t1Type <- infer' c e t1 
                             t2Type <- infer' c e t2 
 
                             case t1Type of
                                NatT -> case t2Type of
                                          ListT -> ret ListT
                                          _     -> matchError ListT t2Type
                                
                                _    -> matchError NatT t1Type


infer' c e (RecL t1 t2 t3) = do t1Type <- infer' c e t1 
                                t2Type <- infer' c e t2 
                                t3Type <- infer' c e t3

                                case t3Type of
                                   ListT ->  case t2Type of
                                               FunT NatT (FunT ListT (FunT t1Type' t1Type'')) -> if t1Type' == t1Type 
                                                                                                     then  if t1Type == t1Type''
                                                                                                              then ret t1Type
                                                                                                              else matchError t1Type t1Type''
                                                                                                     else matchError t1Type t1Type'
                                               _ -> notfunError t2Type


                                   _    -> matchError ListT t3Type             

-- Modularizar funcion chequeo Recursivo pasandole el tipo que espera para t3.                       

                      

