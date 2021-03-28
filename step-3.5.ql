/**
 * @kind path-problem
 */

import DataFlow::PathGraph
import go
import semmle.go.dataflow.DataFlow
import semmle.go.controlflow.IR
import semmle.go.dataflow.internal.DataFlowPrivate
import semmle.go.controlflow.ControlFlowGraph
import semmle.go.controlflow.ControlFlowGraphImpl

Expr resultExpr(FuncDecl f) {
  exists(DataFlow::ResultNode r |
    f = r.getRoot() and
    r.asExpr() = result
  )
}

boolean errorCheckExpr(Expr e) {
  e.(NeqExpr).getAnOperand().(Ident).getName() = "ErrNone" and result = true
  or
  e.(EqExpr).getAnOperand().(Ident).getName() = "ErrNone" and result = false
  or
  result = errorCheckExpr(resultExpr(e.(CallExpr).getTarget().getFuncDecl()))
}

ControlFlow::Node getPreFinalNode(ControlFlow::Node node) {
  result = node.getASuccessor+() and
  result.getASuccessor() instanceof ExitNode
}

predicate hasNilReturn(ControlFlow::Node node) {
  exists(IR::ReturnInstruction ri, ReturnStmt rs |
    node.getASuccessor+() = ri and
    ri.getReturnStmt() = rs and
    (
      rs.getAnExpr().getType() instanceof NilLiteralType
      or
      exists(ReturnStmt nestedNilReturn |
        nestedNilReturn.getEnclosingFunction().getACall().asExpr() = rs.getAnExpr().(CallExpr) and
        nestedNilReturn.getAnExpr().getType() instanceof NilLiteralType
      )
    )
  )
}

class FlowsFromErrorSource extends DataFlow::Configuration {
  FlowsFromErrorSource() { this = "FlowsFromErrorSource" }

  override predicate isSource(DataFlow::Node source) {
    any(Function f | f.getName() = "errorSource" | f.getACall()) = source
  }

  override predicate isSink(DataFlow::Node sink) {
    any(Expr errorTest, ControlFlow::ConditionGuardNode errorNode,
      ControlFlow::ConditionGuardNode noErrorNode, boolean thenIsErrorBranch |
      thenIsErrorBranch = errorCheckExpr(errorTest) and
      errorNode.ensures(DataFlow::exprNode(errorTest), thenIsErrorBranch) and
      noErrorNode.ensures(DataFlow::exprNode(errorTest), thenIsErrorBranch.booleanNot()) and
      (
        exists(ControlFlow::Node commonPrefinal |
          commonPrefinal = getPreFinalNode(errorNode) and
          commonPrefinal = getPreFinalNode(noErrorNode) and
          not commonPrefinal instanceof IR::ReturnInstruction
        )
        or
        hasNilReturn(errorNode)
      )
    |
      errorTest
    ) = sink.asExpr()
  }

  override predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(EqualityTestExpr e |
      e.getAnOperand() = pred.asExpr() and
      e = succ.asExpr()
    )
  }
}

from FlowsFromErrorSource flow, DataFlow::PathNode src, DataFlow::PathNode snk
where flow.hasFlowPath(src, snk)
select snk, src, snk, "Does not return despite error"