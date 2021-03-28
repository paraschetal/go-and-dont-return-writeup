import go
 
from Ident i, Expr e, IfStmt s
where i.getName() = "ErrNone" and e.(EqualityTestExpr).getAnOperand() = i and s.getCond() = e
select s