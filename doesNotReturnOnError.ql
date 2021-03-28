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

//To check valid error sources.
//can be expanded upon depending on database
predicate isErrorSource(Function f){
    f.getName() = "errorSource" or
    f.getName() = "isReqAuthenticated"
}

//To get the result expression for a FuncDecl
Expr resultExpr(FuncDecl f) {
  exists(DataFlow::ResultNode r |
    f = r.getRoot() and
    r.asExpr() = result
  )
}

//Checks if the expression tests for error:
//(directly or is a function call which in-turn has the error-test in return)
//Also returns whether the boolean value of the conditional should be true or false for error or not respectively
boolean errorCheckExpr(Expr e) {
  e.(NeqExpr).getAnOperand().(Ident).getName() = "ErrNone" and result = true
  or
  e.(EqExpr).getAnOperand().(Ident).getName() = "ErrNone" and result = false
  or
  result = errorCheckExpr(resultExpr(e.(CallExpr).getTarget().getFuncDecl())) //if wrapped function
}

//gets the node before the exit node for the flow originating from the param
ControlFlow::Node getPreFinalNode(ControlFlow::Node node) {
  result = node.getASuccessor+() and
  result.getASuccessor() instanceof ExitNode
}

//checks if return node of the control-flow returns a nil value
predicate hasNilReturn(ControlFlow::Node node) {
  exists(IR::ReturnInstruction ri, ReturnStmt rs |
    node.getASuccessor+() = ri and
    ri.getReturnStmt() = rs and
    (
      (rs.getAnExpr().getType() instanceof NilLiteralType and //checks for nil return value
      (count(rs.getAnExpr())=1 //Heuristics: checks if it returns nil and is the only return
      or                       //(as there may be other variables being returned)
      rs.getAnExpr().getStringValue()="")) //This is for func multiReturnBad() in checkReturnValue.go which returns "", nil.
      or
      exists(ReturnStmt nestedNilReturn | //If nil is being returned in a wrapped/nested way
        nestedNilReturn.getEnclosingFunction().getACall().asExpr() = rs.getAnExpr().(CallExpr) and
        nestedNilReturn.getAnExpr().getType() instanceof NilLiteralType
      )
    )
  )
}

//Checks if the commonNode from the error and non-error branch is valid
predicate validCommonNode(ControlFlow::Node commonNode){
  not(commonNode instanceof IR::ReturnInstruction) and //it shouldn't be a return instruction otherwise two cases in logicalOperators.go get flagged
  not exists(DeferStmt d|MkExprNode(d.getAChildExpr()) = commonNode) and //it shouldn't be a defered node - otherwise false-positives in minio db
  not (commonNode instanceof MkResultReadNode) //shouldn't be an implicit read (of results) node - otherwise false-positives in minio db
}


//DataFlow configuration class for the data flow from error source(function call) to sink(conditional expression which does not return despite error)
class FlowsFromErrorSource extends DataFlow::Configuration {
  FlowsFromErrorSource() { this = "FlowsFromErrorSource" }

  //checks if source is a function call to an error-source function
  override predicate isSource(DataFlow::Node source) {
    any(Function f | isErrorSource(f) | f.getACall()) = source
  }

  //checks if sink is a conditional which doesn't return despite error
  override predicate isSink(DataFlow::Node sink) {
    any(Expr errorTest, ControlFlow::ConditionGuardNode errorNode,
      ControlFlow::ConditionGuardNode noErrorNode, boolean thenIsErrorBranch |
      thenIsErrorBranch = errorCheckExpr(errorTest) and //does two things: constraints errorTest and return value indicates which branch is error and which is no-error
      errorNode.ensures(DataFlow::exprNode(errorTest), thenIsErrorBranch) and //ConditionGuardNode for the error branch
      noErrorNode.ensures(DataFlow::exprNode(errorTest), thenIsErrorBranch.booleanNot()) and //ConditionGuardNode for the no-error branch
      (
        exists(ControlFlow::Node commonPrefinal | //checks if the control-flow from error and no-error branches overlaps at a common node right before the exit node
          commonPrefinal = getPreFinalNode(errorNode) and
          commonPrefinal = getPreFinalNode(noErrorNode) and
          validCommonNode(commonPrefinal)
        )
        or
        hasNilReturn(errorNode) //checks if the error branch returns nil
      )
    |
      errorTest
    ) = sink.asExpr()
  }

  //adds a data-flow step from an operand to its equality test expression
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