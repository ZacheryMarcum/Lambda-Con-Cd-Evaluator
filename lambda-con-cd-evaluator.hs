import Control.Monad
import Data.Maybe (isNothing)

-- Original inspiration for design came from these links
-- https://bor0.wordpress.com/2019/03/15/writing-a-simple-evaluator-and-type-checker-in-haskell/
-- https://bor0.wordpress.com/2019/03/19/writing-a-lambda-calculus-evaluator-in-haskell/
type VarName = String

data Expression =
    -- Free variable
    ExVar VarName
    -- Bound variable, specified as Term
    | ExDataVal DataVal
    | ExAbstraction VarName Expression
    | ExApplication Expression Expression
    | ExIfThenElse Expression Expression Expression
    | IsInt Expression
    | IsRational Expression
    | IsReal Expression
    | IsBool Expression
    | IsString Expression
    | Equal Expression Expression
    | Greater Expression Expression
    | Plus Expression Expression
    | Superscript Expression Contract
    | Subscript Expression [Contract]
    | Violation String
    deriving (Eq, Show)


exShow :: Expression -> Int -> String
exShow (ExVar v) x = "(ExVar" ++ " " ++ show v ++ ")"
exShow (ExDataVal dv) x = "(ExDataVal" ++ " " ++ show dv ++ ")"
exShow (ExAbstraction v exp) x = "(ExAbstraction" ++ " " ++ show v
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (ExApplication exp1 exp2) x = "(ExApplication"
    ++ newLine (x + tab) ++ exShow exp1 (x + tab)
    ++ newLine (x + tab) ++ exShow exp2 (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (ExIfThenElse exp1 exp2 exp3) x = "(ExIfThenElse"
    ++ newLine (x + tab) ++ exShow exp1 (x + tab)
    ++ newLine (x + tab) ++ exShow exp2 (x + tab)
    ++ newLine (x + tab) ++ exShow exp3 (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (IsInt exp) x = "(IsInt"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (IsRational exp) x = "(IsRational"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (IsReal exp) x = "(IsReal"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (IsBool exp) x = "(IsBool"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (IsString exp) x = "(IsString"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (Equal exp1 exp2) x = "(Equal"
    ++ newLine (x + tab) ++ exShow exp1 (x + tab)
    ++ newLine (x + tab) ++ exShow exp2 (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (Greater exp1 exp2) x = "(Greater"
    ++ newLine (x + tab) ++ exShow exp1 (x + tab)
    ++ newLine (x + tab) ++ exShow exp2 (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (Plus exp1 exp2) x = "(Plus"
    ++ newLine (x + tab) ++ exShow exp1 (x + tab)
    ++ newLine (x + tab) ++ exShow exp2 (x + tab)
    ++ newLine (x + tab)
    ++ newLine x ++ ")"
exShow (Superscript exp con) x = "(Superscript"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab) ++ conShow con (x + tab)
    ++ newLine x ++ ")"
exShow (Subscript exp l) x = "(Subscript"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine (x + tab) ++ conListShow l (x + tab)
    ++ newLine x ++ ")"
exShow (Violation s) x = "(Violation"
    ++ newLine (x + tab) ++ s
    ++ newLine x ++ ")"

conShow :: Contract -> Int -> String
conShow (ConPred (ExAbstraction str _)) x = "(ConPred " ++ str ++ ")"
conShow (ConPred exp) x = "(ConPred"
    ++ newLine (x + tab) ++ exShow exp (x + tab)
    ++ newLine x ++ ")"
conShow (ConFunc c1 c2) x = "(ConFunc"
    ++ newLine (x + tab) ++ conShow c1 (x + tab)
    ++ newLine (x + tab) ++ conShow c2 (x + tab)
    ++ newLine x ++ ")"


conListShow :: [Contract] -> Int -> String
conListShow [] x = "[]"
conListShow ls x = "[" ++ newLine (x + tab) ++ conListRecurse ls (x + tab) ++ newLine x ++ "]"
    where
        conListRecurse [] x = ""
        conListRecurse (c:cs) x = conShow c x ++ newLine x ++ conListRecurse cs x


newLine :: Int -> String
newLine x = "\n" ++ concat (replicate x " ")

tab :: Int
tab = 4

data DataVal =
    ValBool Bool
    | ValInt Int
    | ValRational Rational
    | ValReal Double
    | ValString String
    deriving (Eq, Show)

data Contract =
    -- Must be an abstraction expression
    ConPred Expression
    | ConFunc Contract Contract
    deriving (Eq, Show)

hasSubscriptExp :: Expression -> Bool
hasSubscriptExp (Subscript _ _) = True
hasSubscriptExp (ExVar _) = False
hasSubscriptExp (ExAbstraction _ exp) = hasSubscriptExp exp
hasSubscriptExp (ExApplication exp1 exp2) = hasSubscriptExp exp1 || hasSubscriptExp exp2
hasSubscriptExp (ExIfThenElse exp1 exp2 exp3) = hasSubscriptExp exp1 || hasSubscriptExp exp2 || hasSubscriptExp exp3
hasSubscriptExp (IsInt exp) = hasSubscriptExp exp
hasSubscriptExp (IsRational exp) = hasSubscriptExp exp
hasSubscriptExp (IsReal exp) = hasSubscriptExp exp
hasSubscriptExp (IsBool exp) = hasSubscriptExp exp
hasSubscriptExp (IsString exp) = hasSubscriptExp exp
hasSubscriptExp (Equal exp1 exp2) = hasSubscriptExp exp1 || hasSubscriptExp exp2
hasSubscriptExp (Greater exp1 exp2) = hasSubscriptExp exp1 || hasSubscriptExp exp2
hasSubscriptExp (Plus exp1 exp2) = hasSubscriptExp exp1 || hasSubscriptExp exp2
hasSubscriptExp (Superscript exp _) = hasSubscriptExp exp
hasSubscriptExp (Violation _) = False

step :: Expression -> Expression
step (Superscript (Violation s) _) = Violation s
step (Subscript (Violation s) _) = Violation s

-- Rule 2
step orig@(Superscript (Subscript exp conList) con@(ConPred pred))
    | reducible exp = Superscript (Subscript (step exp) conList) con
    | otherwise = ExIfThenElse
        (ExApplication
            pred
            (Subscript exp [])
        )
        (Subscript exp (con:conList))
        (Violation "Rule 2 violation")
-- Rule 1
step orig@(Superscript exp con@(ConPred pred))
    | reducible exp = Superscript (step exp) con
    | otherwise = ExIfThenElse
        (ExApplication
            pred
            exp
        )
        exp
        (Violation "Rule 1 violation")
-- Rule 3
step orig@(Superscript (Subscript exp conList) con@(ConFunc _ _))
    | reducible exp = Superscript (step (Subscript exp conList)) con
    | otherwise = Subscript orig []

-- Rule 4
step orig@(Subscript (Superscript (Subscript exp ((ConPred pred):innerList)) funcCon@(ConFunc _ _)) outerList)
    | reducible exp = Subscript (step (Superscript (Subscript exp []) funcCon)) outerList
    | otherwise = ExIfThenElse
        (ExApplication
            pred
            (Subscript
                (Superscript
                    (unwrap exp)
                    funcCon
                )
                []
            )
        )
        (Subscript (Superscript (Subscript exp innerList) funcCon) (ConPred pred:outerList))
        (Violation "Rule 4 violation")
    where
        unwrap :: Expression -> Expression
        unwrap (Superscript exp (ConFunc _ _)) = unwrap exp
        unwrap exp@(ExAbstraction _ _) = exp
        unwrap exp = exp
-- Rule 5
step orig@(Subscript (Superscript (Subscript exp []) funcCon@(ConFunc _ _)) conList)
    | reducible exp = Subscript (step (Superscript (Subscript exp []) funcCon)) conList
    | otherwise = Subscript (Superscript exp funcCon) conList
-- Rule 6
step orig@(ExApplication left@(Subscript (Superscript exp funcCon@(ConFunc c1 c2)) conList) val)
    | reducible left = ExApplication (step left) val
    | reducible exp = ExApplication (Subscript (step (Superscript exp (ConFunc c1 c2))) conList) val
    | reducible val = ExApplication left (step val)
    | otherwise = Superscript (ExApplication (Subscript exp []) (Superscript val c1)) c2
-- Rule 7
step (ExApplication left@(Subscript absExp@(ExAbstraction _ _) _) val)
    | reducible left = ExApplication (step left) val
    | reducible val = ExApplication left (step val)
    | otherwise = ExApplication absExp val

-- Behavioral Patch
step (Subscript (Subscript exp innerList) outerList) = Subscript exp (innerList ++ outerList)

-- ExVar
-- Doesn't get reduced without rule

-- ExDataVal
-- Doesn't get reduced without rule

-- ExAbstraction
-- Doesn't get reduced without rule

-- ExApplication
step (ExApplication (Violation str) _) = Violation str
step (ExApplication _ (Violation str)) = Violation str
step (ExApplication funcExp inputExp)
    | reducible funcExp = ExApplication (step funcExp) inputExp
    | reducible inputExp = ExApplication funcExp (step inputExp)
    | otherwise = case funcExp of
        ExAbstraction varName absBody -> subst varName absBody inputExp
        _ -> Violation "Invalid abstraction expression"

-- ExIfThenElse
step (ExIfThenElse (Violation str) _ _) = Violation str
step (ExIfThenElse _ (Violation str) _) = Violation str
step (ExIfThenElse guardExp expT expF) = case guardExp of
    (ExDataVal (ValBool b)) -> if b
        then expT
        else expF
    -- Else, guardExp is not boolean or needs to be further reduced
    _ -> ExIfThenElse (step guardExp) expT expF

-- Built-in functions
-- IsInt
step (IsInt (Violation str)) = Violation str
step (IsInt exp) = if irreducible exp
    then case exp of
        ExDataVal (ValInt _) -> exTrue
        _ -> exFalse
    else IsInt (step exp)
-- IsRational
step (IsRational (Violation str)) = Violation str
step (IsRational exp) = if irreducible exp
    then case exp of
        ExDataVal (ValInt _) -> exTrue
        ExDataVal (ValRational _) -> exTrue
        _ -> exFalse
    else IsRational (step exp)
-- IsReal
step (IsReal (Violation str)) = Violation str
step (IsReal exp) = if irreducible exp
    then case exp of
        ExDataVal (ValInt _) -> exTrue
        ExDataVal (ValRational _) -> exTrue
        ExDataVal (ValReal _) -> exTrue
        _ -> exFalse
    else IsReal (step exp)
-- IsBool
step (IsBool (Violation str)) = Violation str
step (IsBool exp) = if irreducible exp
    then case exp of
        ExDataVal (ValBool _) -> exTrue
        _ -> exFalse
    else IsBool (step exp)
-- IsString
step (IsString (Violation str)) = Violation str
step (IsString exp) = if irreducible exp
    then case exp of
        ExDataVal (ValString _) -> exTrue
        _ -> exFalse
    else IsString (step exp)
-- Plus
step (Plus (Violation str) _) = Violation str
step (Plus _ (Violation str)) = Violation str
step (Plus exp1 exp2)
    | reducible exp1 = Plus (step exp1) exp2
    | reducible exp2 = Plus exp1 (step exp2)
    | otherwise = case (exp1, exp2) of
        (ExDataVal (ValInt a), ExDataVal (ValInt b)) -> ExDataVal (ValInt (a + b))
        (ExDataVal (ValRational a), ExDataVal (ValRational b)) -> ExDataVal (ValRational (a + b))
        (ExDataVal (ValReal a), ExDataVal (ValReal b)) -> ExDataVal (ValReal (a + b))
        _ -> Violation "Plus error"
-- Equal
step (Equal (Violation str) _) = Violation str
step (Equal _ (Violation str)) = Violation str
step (Equal exp1 exp2)
    | reducible exp1 = Equal (step exp1) exp2
    | reducible exp2 = Equal exp1 (step exp2)
    | otherwise = case (exp1, exp2) of
        (ExDataVal a, ExDataVal b) -> if a == b
            then exTrue
            else exFalse
        _ -> Violation "Equal error"
-- Greater
step (Greater (Violation str) _) = Violation str
step (Greater _ (Violation str)) = Violation str
step (Greater exp1 exp2)
    | reducible exp1 = Greater (step exp1) exp2
    | reducible exp2 = Greater exp1 (step exp2)
    | otherwise = case (exp1, exp2) of
        (ExDataVal (ValInt a), ExDataVal (ValInt b)) -> if a > b
            then exTrue
            else exFalse
        (ExDataVal (ValRational a), ExDataVal (ValRational b)) -> if a > b
            then exTrue
            else exFalse
        (ExDataVal (ValReal a), ExDataVal (ValReal b)) -> if a > b
            then exTrue
            else exFalse
        _ -> Violation "Greater error"

step (Subscript exp con) = Subscript (step exp) con
step (Superscript exp con) = Superscript (step exp) con
-- No rules apply -> fully reduced
step exp = exp

eval :: Expression -> Expression
eval exp
    | step exp == exp = exp
    | otherwise       = eval $! step exp

irreducible :: Expression -> Bool
irreducible exp = step exp == exp

reducible :: Expression -> Bool
reducible = not . irreducible

-- Substitute VarName in exp1 for exp2
-- For the simplicity of the evaluator, naming conflicts must be avoided by on an expression level
subst :: VarName -> Expression -> Expression -> Expression
subst varName subjectExp substExp = case subjectExp of
    ExVar var -> if varName == var then substExp else subjectExp
    ExAbstraction absVar exp -> ExAbstraction
            absVar
            (subst varName exp substExp)
    ExApplication exp1 exp2 -> ExApplication
        (subst varName exp1 substExp)
        (subst varName exp2 substExp)
    ExIfThenElse exp1 exp2 exp3 -> ExIfThenElse
        (subst varName exp1 substExp)
        (subst varName exp2 substExp)
        (subst varName exp3 substExp)
    Superscript exp con -> Superscript
        (subst varName exp substExp)
        con
    Subscript exp con -> Subscript
        (subst varName exp substExp)
        con
    IsInt exp -> IsInt (subst varName exp substExp)
    IsRational exp -> IsRational (subst varName exp substExp)
    IsReal exp -> IsReal (subst varName exp substExp)
    IsBool exp -> IsBool (subst varName exp substExp)
    IsString exp -> IsString (subst varName exp substExp)
    Plus exp1 exp2 -> Plus
        (subst varName exp1 substExp)
        (subst varName exp2 substExp)
    Equal exp1 exp2 -> Equal
        (subst varName exp1 substExp)
        (subst varName exp2 substExp)
    Greater exp1 exp2 -> Greater
        (subst varName exp1 substExp)
        (subst varName exp2 substExp)
    _ -> subjectExp

---------------
-- Functions --
---------------
exId:: String -> Expression
exId s = ExAbstraction ("idInp" ++ s) (ExVar ("idInp" ++ s))
exId' :: String -> Expression
exId' s = ExAbstraction ("id'Inp" ++ s) (Plus (Plus (ExVar ("idInp" ++ s)) (ExDataVal (ValInt 1))) (ExDataVal (ValInt (-1)))) 
exZaz :: String -> Expression
exZaz s = ExAbstraction ("zazInp" ++ s)
    (Equal
        (ExDataVal (ValInt 0))
        (ExApplication
            (ExVar ("zazInp" ++ s))
            (ExDataVal (ValInt 0))
            
        )
        
    )
    
exSp :: String -> Expression
exSp s = ExAbstraction ("spInp" ++ s)
    (Greater
        (ExVar ("spInp" ++ s))
        (ExDataVal (ValInt 0))
        
    )
    
exIsInt :: String -> Expression
exIsInt s = ExAbstraction ("exIsIntInp" ++ s) (IsInt (ExVar ("exIsIntInp" ++ s)))
exIsRational :: String -> Expression
exIsRational s = ExAbstraction ("exIsRationalInp" ++ s) (IsRational (ExVar ("exIsRationalInp" ++ s))) 
exIsReal :: String -> Expression
exIsReal s = ExAbstraction ("exIsRealInp" ++ s) (IsReal (ExVar ("exIsRealInp" ++ s))) 
exIsBool :: String -> Expression
exIsBool s = ExAbstraction ("exIsBoolInp" ++ s) (IsBool (ExVar ("exIsBoolInp" ++ s))) 
exIsString :: String -> Expression
exIsString s = ExAbstraction ("exIsStringInp" ++ s) (IsString (ExVar ("exIsStringInp" ++ s))) 
exAny :: String -> Expression
exAny s = ExAbstraction ("anyInp" ++ s) exTrue 

exReturn1 :: String -> Expression
exReturn1 s = ExAbstraction ("return1Inp" ++ s) (ExDataVal (ValInt 1)) 

ex1a1 :: String -> Expression
ex1a1 s = ExAbstraction ("1a1Inp" ++ s)
    (Equal
        (ExApplication
            (ExVar ("1a1Inp" ++ s))
            (ExDataVal (ValInt 1))
        )
        (ExDataVal (ValInt 1)) 
    )

exHalfAtHalf :: String -> Expression
exHalfAtHalf s = ExAbstraction ("halfAtHalfInp" ++ s)
    (Equal
        (ExApplication
            (ExVar ("halfAtHalfInp" ++ s))
            (ExDataVal (ValRational 0.5))
        )
        (ExDataVal (ValRational 0.5))
    )

-- #3
exF1 :: Expression
exF1 = ExAbstraction "exF1Inp"
    (ExApplication
        (Subscript
            (Superscript exG1 (ConFunc (ConPred (exZaz "1")) (ConPred (exAny "4"))))
            []
        )
        (ExVar "exF1Inp")
    )
        

exG1 :: Expression
exG1 = ExAbstraction "exG1Inp"
    (ExApplication
        (ExVar "exG1Inp")
        (ExDataVal (ValInt 5))
    )
    

exF1G1Any :: Expression
exF1G1Any = ExApplication
    (Subscript
        (Superscript exF1 (ConFunc
            (ConFunc (ConPred (exAny "1")) (ConPred (exAny "2")))
            (ConPred (exAny "3"))
        ))
        []
    )
    (Subscript (exId "1") [])
exF1G1 :: Expression
exF1G1 = ExApplication
    (Subscript
        (Superscript exF1 (ConFunc
                (ConFunc (ConPred (exSp "1")) (ConPred (exSp "2")))
                (ConPred (exAny "3")))
        )
        []
    )
    (Subscript (exId "1") [])

-- #4
exF2 :: Expression
exF2 = ExAbstraction "exF2Inp"
    (ExApplication
        (Subscript
            (Superscript exG1 (ConFunc
                (ConFunc (ConPred (exSp "1")) (ConPred (exSp "2")))
                (ConPred (exAny "3"))
            ))
            []
        )
        (ExVar "exF2Inp")
    )

exF2G2 :: Expression
exF2G2 = ExApplication
    (Subscript
        (Superscript exF2 (ConFunc (ConPred (exZaz "1")) (ConPred (exAny "4"))))
        []
    )
    (Subscript (exId "1") [])

-------------------------
-- Pre-built contracts --
-------------------------
-- Each contract is tagged with a unique string to avoid any possible conflicts
zazAny :: Contract
zazAny = ConFunc (ConPred (exZaz "1")) (ConPred (exAny "1"))
ratToRatAny :: Contract
ratToRatAny = ConFunc (ConFunc (ConPred (exIsRational "2")) (ConPred (exIsRational "202"))) (ConPred (exAny "2"))
realToRealAny :: Contract
realToRealAny = ConFunc (ConFunc (ConPred (exIsReal "3")) (ConPred (exIsReal "303"))) (ConPred (exAny "3"))
oneOneToAny :: Contract
oneOneToAny = ConFunc (ConPred (ex1a1 "4")) (ConPred (exAny "4"))
realToSpAny :: Contract
realToSpAny = ConFunc (ConFunc (ConPred (exIsReal "5")) (ConPred (exSp "5"))) (ConPred (exAny "5"))
anyHalfAtHalf :: Contract
anyHalfAtHalf = ConFunc (ConPred (exAny "6")) (ConPred (exHalfAtHalf "6"))
anyRatToRat :: Contract
anyRatToRat = ConFunc (ConPred (exAny "7")) (ConFunc (ConPred (exIsRational "7")) (ConPred (exIsRational "707")))
anyIntToInt :: Contract
anyIntToInt = ConFunc (ConPred (exAny "8")) (ConFunc (ConPred (exIsInt "8")) (ConPred (exIsInt "808")))
anyZaz :: Contract
anyZaz = ConFunc (ConPred (exAny "9")) (ConPred (exZaz "9"))
spToSpAny :: Contract
spToSpAny = ConFunc (ConFunc (ConPred (exSp "10")) (ConPred (exSp "10010"))) (ConPred (exAny "10"))
anySpToSp :: Contract
anySpToSp = ConFunc (ConPred (exAny "11")) (ConFunc (ConPred (exSp "11")) (ConPred (exSp "11011")))

-- Long examples
lFGHIJ :: Expression
lFGHIJ = ExApplication
    (Subscript
        (Superscript
            (ExAbstraction "lFInput"
                (ExApplication
                    (Subscript
                        (Superscript
                            (ExAbstraction "lGInput"
                                (ExApplication
                                    (Subscript
                                        (Superscript
                                            (ExAbstraction "lHInput"
                                                (ExApplication
                                                    (Subscript
                                                        (Superscript
                                                            (ExAbstraction "lIInput"
                                                                (ExApplication
                                                                    (Subscript
                                                                        (Superscript
                                                                            (ExAbstraction "lJInput"
                                                                                (ExApplication
                                                                                    (ExVar "lJInput")
                                                                                    (ExDataVal (ValInt 5))
                                                                                )
                                                                            )
                                                                            realToSpAny
                                                                        )
                                                                        []
                                                                    )
                                                                    (ExVar "lIInput")
                                                                )
                                                            )
                                                            oneOneToAny
                                                        )
                                                        []
                                                    )
                                                    (ExVar "lHInput")
                                                )
                                            )
                                            realToRealAny
                                        )
                                        []
                                    )
                                    (ExVar "lGInput")
                                )
                            )
                            ratToRatAny
                        )
                        []
                    )
                    (ExVar "lFInput")
                )
            )
            zazAny
        )
        []
    )
    (Subscript (exId "1") [])

lFGHI :: Expression
lFGHI = ExApplication
    (Subscript
        (Superscript
            (ExAbstraction "lFInput"
                (ExApplication
                    (Subscript
                        (Superscript
                            (ExAbstraction "lGInput"
                                (ExApplication
                                    (Subscript
                                        (Superscript
                                            (ExAbstraction "lHInput"
                                                (ExApplication
                                                    (Subscript
                                                        (Superscript
                                                            (ExAbstraction "lIInput"
                                                                (ExVar "lIInput")
                                                            )
                                                            anyZaz
                                                        )
                                                        []
                                                    )
                                                    (ExVar "lHInput")
                                                )
                                            )
                                            anyIntToInt
                                        )
                                        []
                                    )
                                    (ExVar "lGInput")
                                )
                            )
                            anyRatToRat
                        )
                        []
                    )
                    (ExVar "lFInput")
                )
            )
            anyHalfAtHalf
        )
        []
    )
    (Subscript (exId "1") [])

lFGHI2 :: Expression
lFGHI2 = ExApplication
    (Subscript
        (Superscript
            (ExAbstraction "lFInput"
                (ExApplication
                    (Subscript
                        (Superscript
                            (ExAbstraction "lGInput"
                                (ExApplication
                                    (Subscript
                                        (Superscript
                                            (ExAbstraction "lHInput"
                                                (ExApplication
                                                    (Subscript
                                                        (Superscript
                                                            (ExAbstraction "lIInput"
                                                                (ExApplication
                                                                    (ExVar "lIInput")
                                                                    (ExDataVal (ValInt (-10)))
                                                                )
                                                            )
                                                            oneOneToAny
                                                        )
                                                        []
                                                    )
                                                    (ExVar "lHInput")
                                                )
                                            )
                                            realToRealAny
                                        )
                                        []
                                    )
                                    (ExVar "lGInput")
                                )
                            )
                            spToSpAny
                        )
                        []
                    )
                    (ExVar "lFInput")
                )
            )
            ratToRatAny
        )
        []
    )
    (Subscript (exId "1") [])

lFGH :: Expression
lFGH = ExApplication
    (Subscript
        (Superscript
            (ExAbstraction "lFInput"
                (ExApplication
                    (Subscript
                        (Superscript
                            (ExAbstraction "lGInput"
                                (ExApplication
                                    (Subscript
                                        (Superscript
                                            (ExAbstraction "lHInput"
                                                (ExApplication
                                                    (ExVar "lHInput")
                                                    (ExDataVal (ValInt 5))
                                                )
                                            )
                                            realToRealAny
                                        )
                                        []
                                    )
                                    (ExVar "lGInput")
                                )
                            )
                            spToSpAny
                        )
                        []
                    )
                    (ExVar "lFInput")
                )
            )
            zazAny
        )
        []
    )
    (Subscript (exReturn1 "1") [])

lFGH2 :: Expression
lFGH2 = ExApplication
    (Subscript
        (Superscript
            (ExAbstraction "lFInput"
                (ExApplication
                    (Subscript
                        (Superscript
                            (ExAbstraction "lGInput"
                                (ExApplication
                                    (Subscript
                                        (Superscript
                                            (ExAbstraction "lHInput"
                                                (ExVar "lHInput")
                                            )
                                            anyIntToInt
                                        )
                                        []
                                    )
                                    (ExVar "lGInput")
                                )
                            )
                            anyZaz
                        )
                        []
                    )
                    (ExVar "lFInput")
                )
            )
            anySpToSp
        )
        []
    )
    (Subscript
        (ExAbstraction "unsatisfactoryHOF"
            (ExAbstraction "retFunc"
                (ExDataVal (ValInt 1))
            )
        )
        []
    )

-----------------
-- Expressions --
-----------------
exTrue :: Expression
exTrue = ExDataVal (ValBool True) 
exFalse :: Expression
exFalse = ExDataVal (ValBool False) 

-----------------
-- Evaluations --
-----------------
exF1G1Stepped :: IO ()
exF1G1Stepped = steppedLoop exF1G1

exF1G1AnyStepped :: IO ()
exF1G1AnyStepped = steppedLoop exF1G1Any

exF2G2Stepped :: IO ()
exF2G2Stepped = steppedLoop exF2G2

lFGHIJStepped :: IO ()
lFGHIJStepped = steppedLoop lFGHIJ

lFGHIStepped :: IO ()
lFGHIStepped = steppedLoop lFGHI

lFGHI2Stepped :: IO ()
lFGHI2Stepped = steppedLoop lFGHI2

lFGHStepped :: IO ()
lFGHStepped = steppedLoop lFGH

lFGH2Stepped :: IO ()
lFGH2Stepped = steppedLoop lFGH2

steppedLoop :: Expression -> IO ()
steppedLoop exp = do
    putStr "\n-------------------------------------------\n"
    putStr (exShow exp 0)
    -- print (step exp)
    -- print (exp == step exp)
    _ <- getLine
    when (step exp /= exp) (steppedLoop (step exp))
