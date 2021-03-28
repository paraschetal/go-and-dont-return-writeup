/**
 * @kind path-problem
 */

import DataFlow::PathGraph
import go
import semmle.go.dataflow.DataFlow

class FlowsFromErrorSource extends DataFlow::Configuration {
  FlowsFromErrorSource() { this = "FlowsFromErrorSource" }

  override predicate isSource(DataFlow::Node source) {
    any(Function f | f.getName() = "errorSource" | f.getACall()) = source
  }

  override predicate isSink(DataFlow::Node sink) {
    any(EqualityTestExpr e, IfStmt i, Ident errnone |
      i.getCond() = e and
      e.getAnOperand() = errnone and
      errnone.getName() = "ErrNone" and
      (
        e.getPolarity() = false and
        not exists(ReturnStmt r | r = i.getThen().getAChildStmt())
        or
        e.getPolarity() = true and
        not exists(ReturnStmt r | r = i.getElse().getAChildStmt())
      )
    |
      e.getAnOperand()
    ) = sink.asExpr()
  }
}

from FlowsFromErrorSource flow, DataFlow::PathNode src, DataFlow::PathNode snk
where flow.hasFlowPath(src, snk)
select snk, src, snk, "Does not return despite error"
