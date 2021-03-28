/**
 * @kind path-problem
 */

import DataFlow::PathGraph
import go
import semmle.go.dataflow.DataFlow

class FlowsFromIsReqAuth extends DataFlow::Configuration {
  FlowsFromIsReqAuth() { this = "FlowsFromIsReqAuth" }

  override predicate isSource(DataFlow::Node source) {
    any(Function f | f.getName() = "isReqAuthenticated" | f.getACall()) = source
  }

  override predicate isSink(DataFlow::Node sink) {
    any(EqualityTestExpr e, IfStmt i |
      e.getAnOperand().(Ident).getName() = "ErrNone" and
      not exists(ReturnStmt r | r = i.getThen().getAChildStmt()) and
      i.getCond() = e
    |
      e.getAnOperand()
    ) = sink.asExpr()
  }
}

from FlowsFromIsReqAuth flow, DataFlow::PathNode src, DataFlow::PathNode snk
where flow.hasFlowPath(src, snk)
select snk, src, snk, "True bug"
