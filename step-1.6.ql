import go
 
from Ident i, Expr e, IfStmt s
where i.getName() = "ErrNone" and e.(EqualityTestExpr).getAnOperand() = i and s.getCond() = e
    and not exists(ReturnStmt r | r=s.getThen().getAChildStmt())
select s