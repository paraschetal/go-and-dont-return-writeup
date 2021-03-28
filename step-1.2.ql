import go
 
from Ident i, Expr e
where i.getName() = "ErrNone" and e.(EqualityTestExpr).getAnOperand() = i
select e