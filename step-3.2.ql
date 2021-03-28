/**
 * @kind path-problem
 */

import DataFlow::PathGraph
import go
import semmle.go.dataflow.DataFlow
import semmle.go.controlflow.ControlFlowGraphImpl

boolean errorCheckExpr(Expr e) {
  e.(NeqExpr).getAnOperand().(Ident).getName() = "ErrNone" and result = true
  or
  e.(EqExpr).getAnOperand().(Ident).getName() = "ErrNone" and result = false
}

ControlFlow::Node getPreFinalNode(ControlFlow::Node node){
  result = node.getASuccessor+() and
  result.getASuccessor() instanceof ExitNode
}

class FlowsFromErrorSource extends DataFlow::Configuration {
  FlowsFromErrorSource() { this = "FlowsFromErrorSource" }

  override predicate isSource(DataFlow::Node source) {
    any(Function f | f.getName() = "errorSource" | f.getACall()) = source
  }

  override predicate isSink(DataFlow::Node sink) {
    any(EqualityTestExpr errorTest,
      ControlFlow::ConditionGuardNode errorNode,
      ControlFlow::ConditionGuardNode noErrorNode, boolean thenIsErrorBranch |
      thenIsErrorBranch = errorCheckExpr(errorTest) and
      errorNode.ensures(DataFlow::exprNode(errorTest),thenIsErrorBranch) and
      noErrorNode.ensures(DataFlow::exprNode(errorTest), thenIsErrorBranch.booleanNot()) and
      exists(ControlFlow::Node commonPrefinal | commonPrefinal=getPreFinalNode(errorNode) and commonPrefinal=getPreFinalNode(noErrorNode)) 
    |
      errorTest.getAnOperand()
    ) = sink.asExpr()
  }
}

from FlowsFromErrorSource flow, DataFlow::PathNode src, DataFlow::PathNode snk
where flow.hasFlowPath(src, snk)
select snk, src, snk, "Does not return despite error"
