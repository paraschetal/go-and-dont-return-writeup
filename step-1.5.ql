import go
 
from IfStmt i
where not i.getThen().getAChildStmt() instanceof ReturnStmt
select i
