module Analizzatore_sint_2(
parser, progdoll, LKC(..)) where

import Lexer
import Prelude hiding (EQ,exp)

data Exc a = Raise Exception | Return a
type Exception = String
--ETY -> epsilon productions
data LKC = ETY | VAR String | NUM Integer |STRI String | BOO Bool |
           NIL | ADD LKC LKC | SUB LKC LKC | MULT LKC LKC |
           REM LKC LKC | DIV LKC LKC | EQC LKC LKC |
           LEQC LKC LKC | CARC LKC | CDRC LKC | CONSC LKC LKC |
           ATOMC LKC | IFC LKC LKC LKC | LAMBDAC [LKC] LKC |
           CALL LKC [LKC] | LETC LKC [(LKC,LKC)] |
           LETRECC LKC [(LKC, LKC)] deriving(Show, Eq)

instance Show a => Show (Exc a) where
 show (Raise e)= "ERRORE:" ++ e
 show (Return x) = "RAGGIUNTO:" ++ (show x)

instance Monad Exc where
 return x  = Return x
 (Raise e) >>= q   = Raise e
 (Return x) >>= q  = q x 

raise :: Exception -> Exc a
raise e = Raise e


rec_key::[Token]-> Exc ([Token], Bool)
rec_key ((Keyword LET):b)    = Return (b, True)
rec_key ((Keyword LETREC):b) = Return (b, False)
rec_key (a:b)                 = Raise ("trovato " ++ show(a) ++", atteso LET o LETREC")
rec_key  x                   = Raise ("ERRORE STRANO"  ++  show(x))


rec_in::[Token]->Exc[Token]
rec_in ((Keyword IN):b)= Return b
rec_in (a:b)           = Raise ("trovato " ++ show(a) ++ ", atteso IN")

rec_end::[Token]->Exc[Token]
rec_end ((Keyword END):b)= Return b 
rec_end (a:b)            = Raise ("trovato " ++ show(a) ++ ", atteso END")


rec_then ((Keyword THEN):b)= Return b
rec_then (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso THEN")


rec_else ((Keyword ELSE):b)= Return b
rec_else (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")


rec_lp ((Symbol LPAREN):b)=Return b 
rec_lp (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")


rec_rp ((Symbol RPAREN):b)=Return b 
rec_rp (a:b)              = Raise ("trovato " ++ show(a) ++ ", attesa )")



rec_virg ((Symbol VIRGOLA):b)=Return  b 
rec_virg (a:b)               = Raise ("trovato " ++ show(a) ++ ", attesa ,")



rec_equals ((Symbol EQUALS):b)= Return b 
rec_equals (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso =")


progdoll::[Token] -> String
progdoll x= show(prog x)

parser::[Token]-> LKC
parser s = case prog s of Return ([Symbol DOLLAR], x) -> x

             
prog:: [Token] -> Exc ([Token], LKC)
prog a = do 
         (x, lt)<-rec_key a
         (y, lkc1_lst)<-bind x
         z<-rec_in y
         (w, lkc2)<-exp z
         k<-rec_end w
         if lt then Return (k, (LETC lkc2 lkc1_lst))
            else Return (k, (LETRECC lkc2 lkc1_lst))
   
 
exp::[Token]->Exc([Token], LKC)
exp a@((Keyword LET):b)    = (prog a)
exp a@((Keyword LETREC):b) = (prog a)
exp ((Keyword LAMBDA):b)   = do --lambda(Seq_var)Exp
                                y<-rec_lp b      
                                (x, lkc1_lst)<-seq_var y    
                                z<-rec_rp x      
                                (k, lkc2)<-exp z
                                Return (k, (LAMBDAC lkc1_lst lkc2))  --lista parametri formali, espressione

exp ((Operator CONS):b)    = do --OPP(Seq_exp) -> 2 parametri
                                x<-rec_lp b
                                (y, lkc1)<-exp x   
                                z<-rec_virg y
                                (w, lkc2)<-exp z
                                k<-rec_rp w
                                Return(k, (CONSC lkc1 lkc2))

exp ((Operator LEQ):b)     = do --OPP(Seq_exp)-> 2 parametri
                                x<-rec_lp b
                                (y, lkc1)<-exp x    
                                z<-rec_virg y
                                (w, lkc2)<- exp z
                                k<-rec_rp w
                                Return(k, (LEQC lkc1 lkc2))

exp ((Operator EQ):b)      = do
                                x<-rec_lp b
                                (y, lkc1)<-exp x    
                                z<- rec_virg y
                                (w, lkc2)<-exp z
                                k<-rec_rp w
                                Return(k, (EQC lkc1 lkc2))

exp ((Operator CAR):b)      = do    --OPP Seq_exp -> 1 parametro
                              (x, lkc) <- exp b
                              Return(x, (CARC lkc))
exp ((Operator CDR):b)      = do    
                              (x, lkc) <- exp b
                              Return(x, (CDRC lkc))   
exp ((Operator ATOM):b)     = do    
                              (x, lkc) <- exp b
                              Return(x, (ATOMC lkc))     
exp ((Keyword IF):b)        = do
                                (x, lkc1)<- exp b
                                y<-rec_then x
                                (z, lkc2)<-exp y
                                w<-rec_else z
                                (k, lkc3)<-exp w
                                Return(k, (IFC lkc1 lkc2 lkc3))
exp x                       =  expa x

bind ((Id a):b)            =  do
                                x<- rec_equals b
                                (y, lkc1)<- exp x
                                (z, lkc2_lst)<-funx y
                                Return(z, ([((VAR a), lkc1)]++lkc2_lst))

bind (a:_) = Raise ("BINDER CON "++ show(a) ++" A SINISTRA")

funx ((Keyword AND):b)     = bind b
funx a@((Keyword IN):b)    = Return (a, [])
funx (a:_)                 = Raise ("DOPO BINDERS; TROVATO"++show(a))



expa a = do
           (x, lkc)<- funt a
           (y,lkc2)<-fune1 (x,lkc)
           Return(y, lkc2)

funt a = do
           (x, lkc)<-funf a
           (y,lkc2)<-funt1 (x, lkc)
           Return(y, lkc2)


fune1::([Token], LKC)->Exc([Token], LKC)
fune1 (((Symbol PLUS):b), lkc1)    = do
                                     (tk, lkc2)<- funt b
                                     (x, lkc3)<-fune1 (tk, lkc2)
                                     Return(x, (ADD lkc1 lkc3))
fune1 (((Symbol MINUS):b), lkc1)   = do
                                      (tk, lkc2)<- funt b
                                      (x, lkc3)<-fune1 (tk, lkc2)
                                      Return(x, (SUB lkc1 lkc3))
fune1 (x,y)                   = Return (x, y)

funt1::([Token], LKC) -> Exc ([Token], LKC)
funt1 (((Symbol TIMES):b), lkc1)   = do
                                      (x, lkc2)<-funf b
                                      (y, lkc3)<-funt1 (x, lkc2)
                                      Return(y, (MULT lkc1 lkc3))
funt1 (((Symbol DIVISION):b), lkc1)= do
                                      (x, lkc2)<-funf b
                                      (y, lkc3)<-funt1 (x, lkc2)
                                      Return(y, (DIV lkc1 lkc3))
funt1 (x,y)                    = Return (x, y)


funf (a:b)                 = do
                              x<-exp_const a
                              if (x /= ETY) then Return (b,x) 
                                              else fX (a:b)

fX ((Id x):b)              = do
                             (y,lkc)<-fuy b
                             if(lkc /= [NIL]) then 
                                                  Return(y, (CALL (VAR x) lkc))
                             else Return(y, VAR x)

fX ((Symbol LPAREN):b)     = do
                              (tk, lkc)<- expa b
                              x <-rec_rp tk
                              Return(x, lkc)
fX (a:_)                   = Raise ("ERRORE in fX, TROVATO"++ show(a))



exp_const::Token -> Exc(LKC)
exp_const (Number x)  = Return(NUM x)
exp_const Nil         =  Return(NIL)
exp_const (Bool x)         =  Return(BOO x)
exp_const (String x)  =  Return(STRI x)
exp_const  _          = Return(ETY)


fuy ((Symbol LPAREN):b)      =  do
                                 (x,lkc)<-seq_exp b
                                 y<-rec_rp x
                                 Return(y, lkc)

fuy x                        = Return (x,[NIL])


-- da completare ......................................

seq_exp :: [Token]-> Exc([Token], [LKC])
seq_exp a@((Symbol RPAREN):b) = Return (a, [])
seq_exp l   = do
               (x, lkc)<-exp l
               (y,lkc2_lst)<-arg_sep x
               Return (y, [lkc] ++ lkc2_lst)

seq_var:: [Token]-> Exc([Token], [LKC])
seq_var ((Id x):b) = do
                      (y, lkc_lst) <- seq_var b
                      Return(y,([VAR x]++lkc_lst))

seq_var a@((Symbol RPAREN):b) = Return (a, [])
seq_var (a:_ ) = Raise("Found " ++ show(a) ++ "in seq_var")

arg_sep :: [Token]-> Exc([Token], [LKC])
arg_sep ((Symbol VIRGOLA):b) = seq_exp(b)
arg_sep a@((Symbol RPAREN):b) = Return (a, [])
arg_sep (a:_) = Raise("Found " ++ show(a) ++ "in arg_sep")

