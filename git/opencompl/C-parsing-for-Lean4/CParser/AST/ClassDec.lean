import CParser.AST.GroupOne
import CParser.AST.GroupTwo
import CParser.AST.GroupThree

open AST
instance : Inhabited PrimaryExpr where default := PrimaryExpr.Constant 0
instance : Inhabited PostfixExpr where default := PostfixExpr.Primary (default : PrimaryExpr)
instance : Inhabited UnaryOp where default := UnaryOp.Address
instance : Inhabited UnaryExpr where default := UnaryExpr.PostFix (default : PostfixExpr)
instance : Inhabited CastExpr where default := CastExpr.Unary (default : UnaryExpr)
instance : Inhabited MultExpr where default := MultExpr.Cast (default : CastExpr)
instance : Inhabited AddExpr where default := AddExpr.Mult (default : MultExpr)
instance : Inhabited ShiftExpr where default := ShiftExpr.Add (default : AddExpr)
instance : Inhabited RelExpr where default := RelExpr.Shift (default : ShiftExpr)
instance : Inhabited EqExpr where default := EqExpr.Rel (default : RelExpr)
instance : Inhabited AndExpr where default := AndExpr.Eq (default : EqExpr)
instance : Inhabited XOrExpr where default := XOrExpr.And (default : AndExpr)
instance : Inhabited IOrExpr where default := IOrExpr.XOr (default : XOrExpr)
instance : Inhabited LAndExpr where default := LAndExpr.IOr (default : IOrExpr)
instance : Inhabited LOrExpr where default := LOrExpr.LAnd (default : LAndExpr)
instance : Inhabited CondExpr where default := CondExpr.LOr (default : LOrExpr)
instance : Inhabited AssmtOp where default := AssmtOp.Assign
instance : Inhabited AssmtExpr where default := AssmtExpr.Cond (default : CondExpr)
instance : Inhabited ArgExprList where default := ArgExprList.AssmtExpr (default : AssmtExpr)
instance : Inhabited Expression where default := Expression.ExprAssmtExpr (default : AssmtExpr)

instance : Inhabited ConstantExpr where default := ConstantExpr.ConExpr (default : CondExpr)
instance : Inhabited DirAbstrDecl where default := DirAbstrDecl.DirAbDecConSqr (default : ConstantExpr)
instance : Inhabited AbstrDecl where default := AbstrDecl.AbstrDirAbDec (default : DirAbstrDecl)
instance : Inhabited IdentList where default := IdentList.Identifier "foo"
instance : Inhabited DirDecl where default := DirDecl.Identifier "foo"
instance : Inhabited TypeQual where default := TypeQual.Const
instance : Inhabited TypeQualList where default := TypeQualList.TypeQual (default : TypeQual)
instance : Inhabited Pointer where default := Pointer.StarTypeQualList (default : TypeQualList)
instance : Inhabited Declarator where default := Declarator.DirDecl (default : DirDecl)
instance : Inhabited Initializer where default := Initializer.AssmtExpr (default : AssmtExpr)
instance : Inhabited InitList where default := InitList.InitList []
instance : Inhabited InitDecl where default := InitDecl.Declarator (default : Declarator)

instance : Inhabited StorClassSpec where default := StorClassSpec.TypeDef
instance : Inhabited DeclSpec where default := DeclSpec.StorClassSpec (default : StorClassSpec)
instance : Inhabited Declaration where default := Declaration.DeclSpec (default : DeclSpec)
instance : Inhabited DeclList where default := DeclList.Decl (default : Declaration)
instance : Inhabited Enumerator where default := Enumerator.Ident "foo"     -- Default for Identifier?
instance : Inhabited EnumList where default := EnumList.Enum (default : Enumerator)
instance : Inhabited EnumSpec where default := EnumSpec.EnumList (default : EnumList)
instance : Inhabited InitDeclList where default := InitDeclList.InitDecl (default : InitDecl)
instance : Inhabited ParamDecl where default := ParamDecl.DeclSpec (default : DeclSpec)
-- instance : Inhabited ParamList where default := ParamList.ParamDecl (default : ParamDecl)
instance : Inhabited ParamList where default := ParamList.ParamList []
instance : Inhabited ParamTypeList where default := ParamTypeList.ParamList (default : ParamList)
instance : Inhabited TypeSpec where default := TypeSpec.Void
instance : Inhabited SpecQualList where default := SpecQualList.TypeSpec (default : TypeSpec)
instance : Inhabited StructDecl where default := StructDecl.Dec (default : Declarator)
instance : Inhabited StructDeclList where default := StructDeclList.StructDecl (default : StructDecl)
instance : Inhabited StructDeclaration where default := StructDeclaration.SpecQualListStructDecList (default : SpecQualList) (default : StructDeclList)
instance : Inhabited StructDeclarationList where default := StructDeclarationList.StructDeclaration (default : StructDeclaration)
instance : Inhabited StructOrUnion where default := StructOrUnion.Struct
instance : Inhabited StructOrUnionSpec where default := StructOrUnionSpec.SoUStructDeclarationList (default : StructOrUnion) (default : StructDeclarationList)
instance : Inhabited TypeName where default := TypeName.SpecQualList (default : SpecQualList)

mutual
partial def primaryExprToString : PrimaryExpr → String
  | .Identifier s => s
  | .Constant c => toString c
  | .StringLit s => "\"" ++ s ++ "\""
  | .BracketExpr e => "(" ++ (exprToString e) ++ ")"

partial def postfixExprToString : PostfixExpr → String
  | .Primary p => primaryExprToString p
  | .SquareBrack p e => (postfixExprToString p) ++ "[" ++ (exprToString e) ++ "]"
  | .CurlyBrack p => (postfixExprToString p) ++ "()"
  | .AEL p ael => (postfixExprToString p) ++ "(" ++ (aelToString ael) ++ ")"
  | .Identifier p s => (postfixExprToString p) ++ "." ++ s
  | .PtrIdent p s => (postfixExprToString p) ++ "->" ++ s
  | .IncOp p => (postfixExprToString p) ++ "++"
  | .DecOp p => (postfixExprToString p) ++ "--"

partial def unaryOpToString : UnaryOp → String
  | .Address => "&"
  | .Indirection => "*"
  | .Plus => "+"
  | .Minus => "-"
  | .Complement => "~"
  | .LogicalNegation => "!"

partial def unaryExprToString : UnaryExpr → String
  | .PostFix p => (postfixExprToString p)
  | .IncUnary p => "++" ++ (unaryExprToString p)
  | .DecUnary p => "--" ++ (unaryExprToString p)
  | .UnaryOpCast o c => (unaryOpToString o) ++ (castExprToString c)
  | .SizeOf u => "sizeof " ++ (unaryExprToString u)
--  | .SizeOfType t => "sizeof(" ++ (typeNametoString t) ++ ")"
  | _ => "not implemented"

partial def castExprToString : CastExpr → String
  | .Unary u => (unaryExprToString u)
--  | .TypeNameCast t c => "(" ++ (typeNametoString t) ++ ")" ++ (castExprToString c)
  | _ => "not implemented"

partial def multExprToString : MultExpr → String
  | .Cast c => (castExprToString c)
  | .MultStar m c => (multExprToString m) ++ " * " ++ (castExprToString c)
  | .MultDiv m c => (multExprToString m) ++ " / " ++ (castExprToString c)
  | .MultMod m c => (multExprToString m) ++ " % " ++ (castExprToString c)

partial def addExprToString : AddExpr → String
  | .Mult m => (multExprToString m)
  | .AddPlus a m => (addExprToString a) ++ " + " ++ (multExprToString m)
  | .AddMinus a m => (addExprToString a) ++ " - " ++ (multExprToString m)

partial def shiftExprToString : ShiftExpr → String
  | .Add a => (addExprToString a)
  | .ShiftLeft s a => (shiftExprToString s) ++ " << " ++ (addExprToString a)
  | .ShiftRight s a => (shiftExprToString s) ++ " >> " ++ (addExprToString a)

partial def relExprToString : RelExpr → String
  | .Shift s => (shiftExprToString s)
  | .RelLesser r s => (relExprToString r) ++ " < " ++ (shiftExprToString s)
  | .RelGreater r s => (relExprToString r) ++ " > " ++ (shiftExprToString s)
  | .RelLE r s => (relExprToString r) ++ " <= " ++ (shiftExprToString s)
  | .RelGE r s => (relExprToString r) ++ " >= " ++ (shiftExprToString s)

partial def eqExprToString : EqExpr → String
  | .Rel r => (relExprToString r)
  | .EqEqual e r => (eqExprToString e) ++ " == " ++ (relExprToString r)
  | .EqNotEqual e r => (eqExprToString e) ++ " != " ++ (relExprToString r)

partial def andExprToString : AndExpr → String
  | .Eq e => (eqExprToString e)
  | .AndAmp a e => (andExprToString a) ++ " & " ++ (eqExprToString e)

partial def xorExprToString : XOrExpr → String
  | .And a => (andExprToString a)
  | .XOrCaret x a => (xorExprToString x) ++ " ^ " ++ (andExprToString a)

partial def iorExprToString : IOrExpr → String
  | .XOr x => (xorExprToString x)
  | .IOrPipe i x => (iorExprToString i) ++ " | " ++ (xorExprToString x)

partial def landExprToString : LAndExpr → String
  | .IOr i => (iorExprToString i)
  | .LAndDblAmp l i => (landExprToString l) ++ " && " ++ (iorExprToString i)

partial def lorExprToString : LOrExpr → String
  | .LAnd l => (landExprToString l)
  | .LOrDblPipe lo la => (lorExprToString lo) ++ " || " ++ (landExprToString la)

partial def condExprToString : CondExpr → String
  | .LOr l => (lorExprToString l)
  | .CondTernary l e c => (lorExprToString l) ++ " ? " ++ (exprToString e) ++ " : " ++ (condExprToString c)

partial def assmtOpToString : AssmtOp → String
  | .Assign => "="
  | .MulAssign => "*="
  | .DivAssign => "/="
  | .ModAssign => "%="
  | .AddAssign => "+="
  | .SubAssign => "-="
  | .LeftAssign => "<<="
  | .RightAssign => ">>="
  | .AndAssign => "&="
  | .XOrAssign => "^="
  | .OrAssign => "|="

partial def assmtExprToString : AssmtExpr → String
  | .Cond c => (condExprToString c)
  | .AssignAssmtOp u ao ae => (unaryExprToString u) ++ " " ++ (assmtOpToString ao) ++ " " ++ (assmtExprToString ae)

partial def aelToString : ArgExprList → String
  | .AssmtExpr a => (assmtExprToString a)
  | .ArgExprListAssign ael ae => (aelToString ael) ++ " , " ++ (assmtExprToString ae)

partial def exprToString : Expression → String
  | .ExprAssmtExpr a => (assmtExprToString a)
  | .ExprAssign e a => (exprToString e) ++ " , " ++ (assmtExprToString a)

partial def constExprToString : ConstantExpr → String
  | .ConExpr c => (condExprToString c)

partial def dirAbstrDeclToString : DirAbstrDecl → String
  | .DirAbDecAbsRnd a => "(" ++ (abstrDeclToString a) ++ ")"
  | .DirAbDecSqr => "[]"
  | .DirAbDecConSqr c => "[" ++ (constExprToString c) ++ "]"
  | .DirAbDecDirSqr d => (dirAbstrDeclToString d) ++ "[]"
  | .DirAbDecDirConst d c => (dirAbstrDeclToString d) ++ "[" ++ (constExprToString c) ++ "]"
  | .DirAbDecRnd => "()"
--  | .DirAbDecDirParamList ptl => "(" ++ (paramTypeListToString ptl) ++ ")"
  | .DirAbDecDirRnd d => (dirAbstrDeclToString d) ++ "()"
--  | .DirAbDecDirParamList d ptl => (dirAbstrDeclToString d) ++ "(" ++ (paramTypeListToString ptl) ++ ")"

partial def abstrDeclToString : AbstrDecl → String
  | .AbstrPtr p => (pointerToString p)
  | .AbstrDirAbDec d => (dirAbstrDeclToString d)
  | .AbstrPtrDirAbDec p d => (pointerToString p) ++ " " ++ (dirAbstrDeclToString d)

partial def identListToString : IdentList → String
  | .Identifier s => s
  | .IdentListIdent i s => (identListToString i) ++ " , " ++ s

partial def dirDeclToString : DirDecl → String
  | .Identifier s => s
  | .DeclRnd d => "(" ++ (declaratorToString d) ++ ")"
  | .DirDecConst d c => (dirDeclToString d) ++ "[" ++ (constExprToString c) ++ "]"
  | .DirDecSqr d => (dirDeclToString d) ++ "[]"
--  | .DirDecParamList d ptl => (dirDeclToString d) ++ "(" ++ (ptlToString ptl) ++ ")"
  | .DirDecIdentList d il => (dirDeclToString d) ++ "(" ++ (identListToString il) ++ ")"
  | .DirDecRnd d => (dirDeclToString d) ++ "()"

partial def tqlToString : TypeQualList → String
  | .TypeQual tq => (typeQualToString tq)
  | .TypeQuaListTypeQuq tql tq => (tqlToString tql) ++ " " ++ (typeQualToString tq)

partial def typeQualToString : TypeQual → String
  | .Const => "const"
  | .Volatile => "volatile"

partial def pointerToString : Pointer → String
  | .Star => "*"
  | .StarTypeQualList tql => "* " ++ (tqlToString tql)
  | .StarPtr p => "* " ++ (pointerToString p)
  | .StarTypeQualListPtr tql p => "* " ++ (tqlToString tql) ++ " " ++ (pointerToString p)

partial def declaratorToString : Declarator → String
  | .PtrDirDecl p d => (pointerToString p) ++ " " ++ (dirDeclToString d)
  | .DirDecl d => (dirDeclToString d)

partial def initListToString : InitList → String
  | .InitList inits => " , ".intercalate (inits.map initializerToString)

partial def initializerToString : Initializer → String
  | .AssmtExpr a => (assmtExprToString a)
  | .InitListCurl il => "{" ++ (initListToString il) ++ "}"
  | .InitListCurlComma il => "{" ++ (initListToString il) ++ ",}"

partial def declarationToString : Declaration → String
  | .DeclSpec d => (declSpecToString d) ++ ";"
  | .DeclSpecInitDecList d i => (declSpecToString d) ++ (initDeclListToString i) ++ ";"

partial def declListToString : DeclList → String
  | .Decl d => (declarationToString d)
  | .DeclListDecl d i => (declListToString d) ++ (declarationToString i)

partial def initDeclListToString : InitDeclList → String
  | .InitDecl d => (initDeclToString d)
  | .InitDeclListInitDecl d i => (initDeclListToString d) ++ " , " ++ (initDeclToString i)

partial def declSpecToString : DeclSpec → String
  | .StorClassSpec d => (storClassSpecToString d)
  | .StorClassSpecDeclSpec d i => (storClassSpecToString d) ++ (declSpecToString i)
  | .TypeSpec d => (typeSpecToString d)
  | .TypeSpecDeclSpec d i => (typeSpecToString d) ++ (declSpecToString i)
  | .TypeQual d => (typeQualToString d)
  | .TypeQualDeclSpec d i => (typeQualToString d) ++ (declSpecToString i)

partial def initDeclToString : InitDecl → String
  | .Declarator d => (declaratorToString d)
  | .DeclInit d i => (declaratorToString d) ++ " = " ++ (initializerToString i)

partial def storClassSpecToString : StorClassSpec → String
  | .TypeDef => "typedef"
  | .Extern => "extern"
  | .Static => "static"
  | .Auto => "auto"
  | .Register => "register"

partial def typeSpecToString : TypeSpec → String
  | .Void
  | .Char => "char"
  | .Short => "short"
  | .Int => "int"
  | .Long => "long"
  | .Float => "float"
  | .Double => "double"
  | .Signed => "signed"
  | .Unsigned => "unsigned"
  | .SoUSpec d => (structOrUnionSpecToString d)
  | .EnumSpec d => (enumSpecToString d)
  | .TypeName => "typename"

partial def structOrUnionSpecToString : StructOrUnionSpec → String
  | .SoUIdentStructDeclarationList a b c => (structOrUnionToString a) ++ b ++ "{" ++ (structDeclarationListToString c) ++ "}"
  | .SoUStructDeclarationList a b => (structOrUnionToString a) ++ "{" ++ (structDeclarationListToString b) ++ "}"
  | .SoUIdent a b => (structOrUnionToString a) ++ b

partial def structOrUnionToString : StructOrUnion → String
  | .Struct => "struct"
  | .Union => "union"

partial def structDeclarationToString : StructDeclaration → String
  | .SpecQualListStructDecList d i => (specQualListToString d) ++ (structDeclListToString i) ++ ";" 

partial def structDeclarationListToString : StructDeclarationList → String
  | .StructDeclaration d => (structDeclarationToString d)
  | .StructDeclListStructDecl d i => (structDeclarationListToString d) ++ (structDeclarationToString i)

partial def enumeratorToString : Enumerator → String
  | .Ident s => s
  | .IdentAssignConst s d => s ++ " = " ++ (constExprToString d)

partial def enumListToString : EnumList → String
  | .Enum d => (enumeratorToString d)
  | .EnumListEnum d i => (enumListToString d) ++ " , " ++ (enumeratorToString i)

partial def enumSpecToString : EnumSpec → String
  | .EnumList d => "enum " ++ "{" ++ (enumListToString d) ++ "}"
  | .IdentEnumList s d => "enum " ++ s ++ "{" ++ (enumListToString d) ++ "}"
  | .EnumIdent s => "enum " ++ s

partial def paramDeclToString : ParamDecl → String
  | .DeclSpecDecl d i => (declSpecToString d) ++ (declaratorToString i)
  | .DeclSpecAbsDecl d i => (declSpecToString d) ++ (abstrDeclToString i)
  | .DeclSpec d => (declSpecToString d)

partial def paramListToString : ParamList → String
  | .ParamList params => " , ".intercalate (params.map paramDeclToString)
--   | .ParamDecl d => (paramDeclToString d)
--   | .ParamListParamDecl d i => (paramListToString d) ++ " , " ++ (paramDeclToString i)

partial def paramTypeListToString : ParamTypeList → String
  | .ParamList d => (paramListToString d)
  | .ParamListEllipsis d => (paramListToString d) ++ " , " ++ "..."

partial def specQualListToString : SpecQualList → String
  | .TypeSpecSpecQualList d i => (typeSpecToString d) ++ (specQualListToString i)
  | .TypeSpec d => (typeSpecToString d)
  | .TypeQualSpecQualList d i => (typeQualToString d) ++ (specQualListToString i)
  | .TypeQual d => (typeQualToString d)

partial def structDeclToString : StructDecl → String
  | .Dec d => (declaratorToString d)
  | .ConstExpr d => ": " ++ (constExprToString d)
  | .DeclConstExpr d i => (declaratorToString d) ++ " : " ++ (constExprToString i)

partial def structDeclListToString : StructDeclList → String
  | .StructDecl d => (structDeclToString d)
  | .StructDecListStructDec d i => (structDeclListToString d) ++ " , " ++ (structDeclToString i)

partial def typeNameToString : TypeName → String
  | .SpecQualList a => (specQualListToString a)
  | .SpecQualListAbsDec a b => (specQualListToString a) ++ (abstrDeclToString b)

end

instance : ToString PrimaryExpr where toString := primaryExprToString
instance : ToString PostfixExpr where toString := postfixExprToString
instance : ToString UnaryOp where toString := unaryOpToString
instance : ToString UnaryExpr where toString := unaryExprToString
instance : ToString CastExpr where toString := castExprToString
instance : ToString MultExpr where toString := multExprToString
instance : ToString AddExpr where toString := addExprToString
instance : ToString ShiftExpr where toString := shiftExprToString
instance : ToString RelExpr where toString := relExprToString
instance : ToString EqExpr where toString := eqExprToString
instance : ToString AndExpr where toString := andExprToString
instance : ToString XOrExpr where toString := xorExprToString
instance : ToString IOrExpr where toString := iorExprToString
instance : ToString LAndExpr where toString := landExprToString
instance : ToString LOrExpr where toString := lorExprToString
instance : ToString CondExpr where toString := condExprToString
instance : ToString AssmtOp where toString := assmtOpToString
instance : ToString AssmtExpr where toString := assmtExprToString
instance : ToString ArgExprList where toString := aelToString
instance : ToString Expression where toString := exprToString

instance : ToString ConstantExpr where toString := constExprToString
instance : ToString DirAbstrDecl where toString := dirAbstrDeclToString
instance : ToString AbstrDecl where toString := abstrDeclToString
instance : ToString IdentList where toString := identListToString
instance : ToString DirDecl where toString := dirDeclToString
instance : ToString TypeQualList where toString := tqlToString
instance : ToString TypeQual where toString := typeQualToString
instance : ToString Pointer where toString := pointerToString
instance : ToString Declarator where toString := declaratorToString
instance : ToString InitList where toString := initListToString
instance : ToString Initializer where toString := initializerToString
instance : ToString InitDecl where toString := initDeclToString

instance : ToString Declaration where toString := declarationToString
instance : ToString DeclList where toString := declListToString
instance : ToString DeclSpec where toString := declSpecToString
instance : ToString Enumerator where toString := enumeratorToString
instance : ToString EnumList where toString := enumListToString
instance : ToString EnumSpec where toString := enumSpecToString
instance : ToString InitDeclList where toString := initDeclListToString
instance : ToString ParamList where toString := paramListToString
instance : ToString ParamTypeList where toString := paramTypeListToString
instance : ToString SpecQualList where toString := specQualListToString
instance : ToString StorClassSpec where toString := storClassSpecToString
instance : ToString StructDecl where toString := structDeclToString
instance : ToString StructDeclaration where toString := structDeclarationToString
instance : ToString StructDeclarationList where toString := structDeclarationListToString
instance : ToString StructDeclList where toString := structDeclListToString
instance : ToString StructOrUnion where toString := structOrUnionToString
instance : ToString StructOrUnionSpec where toString := structOrUnionSpecToString
instance : ToString TypeName where toString := typeNameToString
instance : ToString TypeSpec where toString := typeSpecToString
