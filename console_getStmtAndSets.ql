
import javascript
import ReorderingUtils


from IODependentStmt s, Stmt ess, Stmt lss
where /*stmtInLoop(s) and*/ stmtHasAwait(s) //and stmtDependsOnIO(s) 
and ess = stmtEarliestStmtToSwapWith(s)
and lss = stmtLatestStmtToSwapWith(s)
select s.getLocation().getStartLine(), s.getLocation().getStartColumn(), s.getLocation().getEndLine(), s.getLocation().getEndColumn(), 
     ess.getLocation().getStartLine(), ess.getLocation().getStartColumn(), ess.getLocation().getEndLine(), ess.getLocation().getEndColumn(), 
     lss.getLocation().getStartLine(), lss.getLocation().getStartColumn(), lss.getLocation().getEndLine(), lss.getLocation().getEndColumn(), 
     s.getFile()
