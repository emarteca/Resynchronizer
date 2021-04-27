
import javascript
import semmle.javascript.dataflow.Portals


// Note: this is taken and adapted from an old codeQL implementation of access paths 
// We discuss the extensions in the associated paper
// codeQL implementation: https://github.com/github/codeql/blob/main/javascript/ql/src/semmle/javascript/dataflow/internal/AccessPaths.qll

private import semmle.javascript.dataflow.internal.FlowSteps as FlowSteps

/**
 * A representation of a property name that is either statically known or is
 * the value of an SSA variable.
 */
 private newtype PropertyName =
 StaticPropertyName(string name) { exists(PropAccess pa | name = pa.getPropertyName()) } or
 DynamicPropertyName(SsaVariable var) {
  exists(PropAccess pa | pa.getPropertyNameExpr() = var.getAUse())
}

/**
 * Gets an access to property `name` of access path `base` in basic block `bb`.
 */
 private PropAccess namedPropAccess(AccessPath base, PropertyName name, BasicBlock bb) {
  result.getBase() = base.getAnInstanceIn(bb) and
  (
    name = StaticPropertyName(result.getPropertyName())
    or
    exists(SsaVariable var |
      result.getPropertyNameExpr() = var.getAUse() and
      name = DynamicPropertyName(var)
      )
    )
}

private SsaVariable getRefinedVariable(SsaVariable variable) {
  result = variable.getDefinition().(SsaRefinementNode).getAnInput()
}

private SsaVariable getARefinementOf(SsaVariable variable) { variable = getRefinedVariable(result) }

/**
 * A representation of a (nested) property access on an SSA variable or captured variable
 * where each property name is either constant or itself an SSA variable.
 */
 private newtype TAccessPath =
  /**
   * An access path rooted in an SSA variable.
   *
   * Refinement nodes are treated as no-ops so that all uses of a refined value are
   * given the same access path. Refinement nodes are therefore never treated as roots.
   */
   MkSsaRoot(SsaVariable var) {
    not exists(getRefinedVariable(var)) and
    not var.getSourceVariable().isCaptured() // Handled by MkCapturedRoot
    } or
  /**
   * An access path rooted in a captured variable.
   *
   * The SSA form for captured variables is too conservative for constructing
   * access paths across function boundaries, so in this case we use the source
   * variable as the root.
   */
   MkCapturedRoot(LocalVariable var) { var.isCaptured() } or
  /**
  * access path rooted at a global variable 
  */
  MkGlobalRoot(GlobalVariable var) or
  /**
   * An access path rooted in the receiver of a function.
   */
   MkThisRoot(Function function) { function.getThisBinder() = function } or

 /**
	A PurelyLocalVariable (i.e. LocalVariable that is not captured), that is 
	also an SsaSourceVariable with no corresponding SsaVariable
	(not sure how this is possible, but definitely exists)
 */
 MkPurelyLocalNoSSaRoot(PurelyLocalVariable pvar) {
 	not exists(SsaVariable svar | svar.getSourceVariable() = pvar)
 }
 or 
  /**
   * A property access on an access path.
   */
   MkAccessStep(AccessPath base, PropertyName name) { exists(namedPropAccess(base, name, _)) }

/**
 * A representation of a (nested) property access on an SSA variable or captured variable
 * where each property name is either constant or itself an SSA variable.
 */
 class AccessPath extends TAccessPath {
  /**
   * Gets an expression in `bb` represented by this access path.
   */
   Expr getAnInstanceIn(BasicBlock bb) {
    exists(SsaVariable var |
      this = MkSsaRoot(var) and
      result = getARefinementOf*(var).getAUseIn(bb)
      )
    or
    exists(Variable var |
      this = MkCapturedRoot(var) and
      result = var.getAnAccess() and
      result.getBasicBlock() = bb
      )
    or
    exists(Variable var |
      this = MkGlobalRoot(var) and
      result = var.getAnAccess() and
      result.getBasicBlock() = bb
      )
    or
    exists(ThisExpr this_ |
      this = MkThisRoot(this_.getBinder()) and
      result = this_ and
      this_.getBasicBlock() = bb
      )
    or
    exists(PurelyLocalVariable pvar | 
    	this = MkPurelyLocalNoSSaRoot(pvar) and 
    	result = pvar.getAnAccess() and 
    	result.getBasicBlock() = bb
      )
    or
    exists(AccessPath base, PropertyName name |
      this = MkAccessStep(base, name) and
      result = namedPropAccess(base, name, bb)
      )
  }

  /**
   * Gets an expression represented by this access path.
   */
   Expr getAnInstance() { result = getAnInstanceIn(_) }

  /**
    Get the base of the access path 
  */
  AccessPath getBase() {
    // base cases
    ((this = MkSsaRoot(_) or this = MkThisRoot(_) or this = MkCapturedRoot(_) or this = MkGlobalRoot(_) or this = MkPurelyLocalNoSSaRoot(_)) and result = this)
    // recursive case, with longer access path
    or 
    exists( AccessPath bp | this = MkAccessStep(bp, _) and result = bp.getBase()) 
  }

  
  // check if ap is contained in "this"
  predicate checkPathIsContained(AccessPath ap) {
    this = ap 
    or
    exists( AccessPath bp | this = MkAccessStep(bp, _) and bp.checkPathIsContained( ap))
  }

  pragma[noinline]
  predicate pathEquals(AccessPath ap) {
  	exists(AccessPath tt, AccessPath apt, PropertyName pn | 
     this = MkAccessStep(tt, pn) and 
     ap = MkAccessStep(apt, pn) and
     (tt.pathEquals( apt) or tt = tt.getBase())
     ) 
  }

  predicate pathEqualsBothBase(AccessPath ap, ArgNode arg) {
  	//ap.getBase().getAnInstance() = baseAP.getBase().getAnInstance() and
  	exists(AccessPath tt, AccessPath apt, PropertyName pn | 
     this = MkAccessStep(tt, pn) and 
     ap = MkAccessStep(apt, pn) and
     (tt.pathEqualsBothBase( apt, arg) or tt = tt.getBase() and apt.getAnInstance() = arg.asExpr())
     ) 
  }

  predicate pathEqualsWithBase(AccessPath ap, DataFlow::MethodCallNode mcn) {
  	exists(AccessPath tt, AccessPath apt, PropertyName pn | 
     this = MkAccessStep(tt, pn) and 
     ap = MkAccessStep(apt, pn) and
     (tt.pathEqualsWithBase( apt, mcn) or tt = tt.getBase() and apt.getAnInstance() = mcn.getReceiver().asExpr())
     ) 
  }

  /**
   * Gets a textual representation of this access path.
   */
   string toString() {
    exists(SsaVariable var | this = MkSsaRoot(var) | result = var.getSourceVariable().getName())
    or
    exists(GlobalVariable var | this = MkGlobalRoot(var) | result = var.getName())
    or
    this = MkThisRoot(_) and result = "this"
    or
    exists( PurelyLocalVariable pvar | this = MkPurelyLocalNoSSaRoot(pvar) | result = pvar.getName())
    or
    exists( Variable v | this = MkCapturedRoot( v) | result = v.getName())
    or
    exists(AccessPath base, PropertyName name, string rest |
      rest = "." + any(string s | name = StaticPropertyName(s))
      or
      rest = "[" +
      any(SsaVariable var | name = DynamicPropertyName(var)).getSourceVariable().getName() + "]"
      |
      result = base.toString() + rest and
      this = MkAccessStep(base, name)
      )
  }
}

class ThisRefAccessPath extends AccessPath {
  DataFlow::MethodCallNode mcn;

  ThisRefAccessPath() {
    exists( Function f | 
     //this.getBase() = MkThisRoot(f.getThisBinder()) and 
     mcn.getACallee() = f and
     thisRefInFct(this, f)
     )
  }

     predicate isRefdByStmt(Stmt s) {
      mcn.asExpr().getEnclosingStmt() = s
    }
  }

  class ThisModAccessPath extends ThisRefAccessPath {
   ThisModAccessPath() {
    exists( Function f | 
     mcn.getACallee() = f and
     thisModInFct(this, f)
     )
  }
}

class ThisAccAccessPath extends ThisRefAccessPath {
	ThisAccAccessPath() {
		exists( Function f | 
     mcn.getACallee() = f and
     thisAccInFct(this, f)
     )
	}
}

// create a new class ParamModAccessPath that represents local variables that are modified but that
// correspond to arguments to the function
// like the "this" path, it should be tied to a particular instance of a function call
class ParamRefAccessPath extends AccessPath {
	DataFlow::InvokeNode invk;
	Parameter p;
	ArgNode arg;
	AccessPath argAP;

	ParamRefAccessPath() {
		exists( Function f | 
			arg.getInvk().getACallee() = f and
			localRefInFct(this, f) and
			p.getVariable() = baseLocalVar(this, f) and
			//arg = invk.getAnArgument() and
			argAP.getAnInstance() = arg.asExpr() and 
			FlowSteps::argumentPassing(arg.getInvk(), arg, f, DataFlow::parameterNode(p))
      )
	}

	predicate isRefdByStmt(Stmt s) {
		//invk.asExpr().getEnclosingStmt() = s
		arg.asExpr().getEnclosingStmt() = s
	}

}

class ParamModAccessPath extends ParamRefAccessPath {
	ParamModAccessPath() {
		exists( Function f | 
			arg.getInvk().getACallee() = f and
			localModInFct(this, f) and
			p.getVariable() = baseLocalVar(this, f) and
			//arg = invk.getAnArgument() and
			argAP.getAnInstance() = arg.asExpr() and 
			FlowSteps::argumentPassing(arg.getInvk(), arg, f, DataFlow::parameterNode(p))
      )
	}
}

class ParamAccAccessPath extends ParamRefAccessPath {
	ParamAccAccessPath() {
		exists( Function f | 
			arg.getInvk().getACallee() = f and
			localAccInFct(this, f) and
			p.getVariable() = baseLocalVar(this, f) and
			//arg = invk.getAnArgument() and
			argAP.getAnInstance() = arg.asExpr() and 
			FlowSteps::argumentPassing(arg.getInvk(), arg, f, DataFlow::parameterNode(p))
      )
	}
}

class DynamicPropAccessPath extends AccessPath {
  PropAccess pa;
  DynamicPropAccessPath() {
    not exists( pa.getPropertyName())
    and not exists(SsaVariable svar | pa.getPropertyNameExpr() = svar.getAUse())
    and this.getAnInstance() = pa.getBase()
  }
  PropAccess getPropAcc() { result = pa }
}

class ArgNode extends DataFlow::ValueNode {

	DataFlow::InvokeNode invk; 

	ArgNode() {
		this = invk.getAnArgument()
	}

	DataFlow::InvokeNode getInvk() {
		result = invk
	}
}

// we're replacing oldBase in oldPath by newBase
// example: oldPath = x.a.b.c oldBase = x.a newBase = this
// then, the result would be this.b.c
AccessPath replaceBase( AccessPath oldPath, AccessPath oldBase, AccessPath newBase) {
  (oldPath = oldBase and result = newBase)
  or
  ( not (oldPath = oldBase)
    and
    exists( PropertyName pn | 
      oldPath = MkAccessStep(_, pn) 
      and
      result = replaceBase(oldPath, MkAccessStep(oldBase, pn), MkAccessStep(newBase, pn))
      ))
}

// for the variable assignments that don't get caught as VarDefs for some reason
class VarAssignStmt extends Stmt {
	Variable v;

	VarAssignStmt() {
		exists(AssignExpr ae | this.(ExprStmt).getExpr() = ae and ae.getLhs() = v.getAnAccess())
	}

	Variable getVariable() {
		result = v
	}
}

class SwappableAwaitExpr extends AwaitExpr {
	SwappableAwaitExpr() {
		not this.getParentExpr() instanceof ConditionalExpr
    and 
    not exists( ControlStmtWithTest ct | this.getParentExpr*() = ct.getTest())
    and 
    not this.getEnclosingStmt().getParentStmt*() instanceof ReturnStmt
    and 
    not exists( ArgNode arg | arg.asExpr() = this)
  }
}


// control statements with a condition test
// control statements include: Loops, Ifs, Withs, Trys, Catches, and Switch
// here we exclude try and catch since they don't have a condition check
// and, we merge the predicates to get the condition exprs (since they all have different names)
class ControlStmtWithTest extends ControlStmt {
	Expr test;

	ControlStmtWithTest() {
		this.(LoopStmt).getTest() = test or
		this.(IfStmt).getCondition() = test or
		this.(WithStmt).getExpr() = test or
		this.(SwitchStmt).getExpr() = test 
	}

	Expr getTest() {
		result = test
	}

	// this is just needed for the class to compile
	// since it's an abstract predicate in ControlStmt
	override Stmt getAControlledStmt() {
		result = this.(LoopStmt).getAControlledStmt() or
		result = this.(IfStmt).getAControlledStmt() or
		result = this.(WithStmt).getAControlledStmt() or
		result = this.(SwitchStmt).getAControlledStmt() 
	}
}


// --------------------------------------------------------------------------------------------------------------------------------------- SSAVar 
predicate currentStmtDefSsaVar(SsaVariable svar, Stmt s) {
	svar.getSourceVariable() = s.(DeclStmt).getADecl().getBindingPattern().getVariable()
	or
	svar.getSourceVariable() = s.(VarAssignStmt).getVariable()
}

predicate ssavarDefInTarget(SsaVariable svar, Stmt s) {
	exists(VarDef d | d.getAVariable() = svar.getSourceVariable() and //d = svar.getAUse().getADef() and
    d.getTarget().getEnclosingStmt() = s)
	or 
	currentStmtDefSsaVar(svar, s)
}

predicate ssavarCaseExprMods(SsaVariable svar, Expr e) {
  exists(VarDef d | d.getAVariable() = svar.getSourceVariable() and //d = svar.getAUse().getADef() and
    d.getTarget().getParentExpr*() = e)
}

predicate ssavarAccInTarget(SsaVariable svar, Stmt s) {
	exists(VarAccess d | /*(d.getAVariable() = svar.getAUse().getVariable()*/ d.getVariable() = svar.getSourceVariable() and d.getEnclosingStmt() = s)
}

predicate ssavarCaseExprAccs(SsaVariable svar, Expr e) {
  exists(VarAccess d | /*(d.getAVariable() = svar.getAUse().getVariable()*/ d.getVariable() = svar.getSourceVariable() and d.getParentExpr*() = e)
}

predicate stmtModifiesSSAVar(Stmt s, SsaVariable svar) {
	ssavarDefInTarget(svar, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnModifiesSSAVar( svar, invk.getACallee()) or argModifiesSSAVar(invk.getAnArgument().(DataFlow::FunctionNode), svar)
    or ssavarCaseExprMods(svar, invk.getAnArgument().asExpr())) and
  invk.asExpr().getEnclosingStmt() = s) 
}

predicate stmtAccessesSSAVar(Stmt s, SsaVariable svar) {
	ssavarAccInTarget(svar, s)
	or
	exists( DataFlow::InvokeNode invk | (fnAccessesSSAVar(svar, invk.getACallee()) or argAccessesSSAVar( invk.getAnArgument().(DataFlow::FunctionNode), svar)
    or ssavarCaseExprAccs(svar, invk.getAnArgument().asExpr())) and 
  invk.asExpr().getEnclosingStmt() = s)
}

predicate fnModifiesSSAVar(SsaVariable svar, Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtModifiesSSAVar( s, svar) )
	and
	//not svar.getAUse().getVariable().(LocalVariable).getDeclaringContainer() = f
	not svar.getSourceVariable().getDeclaringContainer() = f
}

predicate fnAccessesSSAVar(SsaVariable svar, Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtAccessesSSAVar( s, svar) )
	and
	//not svar.getAUse().getVariable().(LocalVariable).getDeclaringContainer() = f
	not svar.getSourceVariable().getDeclaringContainer() = f
}

// local (captured) variable case
// --------------------------------------------------------------------------------------------------------------------------------------- LocalVariable
predicate currentStmtDefLocalVar(LocalVariable lvar, Stmt s) {
	s.(DeclStmt).getADecl().getBindingPattern().getVariable() = lvar
	or
	s.(VarAssignStmt).getVariable() = lvar
}

predicate localvarDefInTarget(LocalVariable lvar, Stmt s) {
	exists(VarDef d | d = lvar.getADefinition() and
    d.getTarget().getEnclosingStmt() = s)
	or
	currentStmtDefLocalVar(lvar, s)
}

predicate lvarCaseExprMods(LocalVariable lvar, Expr e) {
  exists(VarDef d | d = lvar.getADefinition() and
    d.getTarget().getParentExpr*() = e)
}

predicate localvarAccInTarget(LocalVariable lvar, Stmt s) {
	exists(VarAccess d | d.getAVariable() = lvar and d.getEnclosingStmt() = s)
}

predicate lvarCaseExprAccs(LocalVariable lvar, Expr e) {
  exists(VarAccess d | d.getAVariable() = lvar and d.getParentExpr*() = e)
}

predicate stmtModifiesLocalVar(Stmt s, LocalVariable lvar) {
	localvarDefInTarget(lvar, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnModifiesLocalVar( lvar, invk.getACallee()) or argModifiesLocalVar(invk.getAnArgument().(DataFlow::FunctionNode), lvar)
    or lvarCaseExprMods(lvar, invk.getAnArgument().asExpr())) and
  invk.asExpr().getEnclosingStmt() = s) 
}

predicate stmtAccsLocalVar(Stmt s, LocalVariable lvar) {
	localvarAccInTarget(lvar, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnAccsLocalVar( lvar, invk.getACallee()) or argAccessesLocalVar( invk.getAnArgument().(DataFlow::FunctionNode), lvar)
    or lvarCaseExprAccs(lvar, invk.getAnArgument().asExpr())) and
  invk.asExpr().getEnclosingStmt() = s) 
}

predicate fnModifiesLocalVar(LocalVariable lvar, Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtModifiesLocalVar( s, lvar) )
	and
	not lvar.getDeclaringContainer() = f
}

predicate fnAccsLocalVar(LocalVariable lvar, Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtAccsLocalVar( s, lvar) )
	and
	not lvar.getDeclaringContainer() = f
}

// global variable case
// --------------------------------------------------------------------------------------------------------------------------------------- GlobalVariable
predicate globalvarDefInTarget(GlobalVariable gvar, Stmt s) {
	exists(VarDef d | d = gvar.getADefinition() and
    d.getTarget().getEnclosingStmt() = s)
	/*or
	s.(DeclStmt).getADecl().getBindingPattern().getVariable() = gvar*/
}

predicate gvarCaseExprMods(GlobalVariable gvar, Expr e) {
  exists(VarDef d | d = gvar.getADefinition() and
    d.getTarget().getParentExpr*() = e)
}

predicate globalvarAccInTarget(GlobalVariable gvar, Stmt s) {
	exists(VarAccess d | d.getAVariable() = gvar and d.getEnclosingStmt() = s)
}

predicate gvarCaseExprAccs(GlobalVariable gvar, Expr e) {
  exists(VarAccess d | d.getAVariable() = gvar and d.getParentExpr*() = e)
}

predicate stmtModifiesGVar(Stmt s, GlobalVariable gvar) {
	globalvarDefInTarget(gvar, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnModifiesGVar( gvar, invk.getACallee()) or argModifiesGVar( invk.getAnArgument().(DataFlow::FunctionNode), gvar)
   or gvarCaseExprMods(gvar, invk.getAnArgument().asExpr())) and
  invk.asExpr().getEnclosingStmt() = s) 
}

predicate stmtAccsGVar(Stmt s, GlobalVariable gvar) {
	globalvarAccInTarget(gvar, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnAccsGVar( gvar, invk.getACallee()) or argAccessesGVar( invk.getAnArgument().(DataFlow::FunctionNode), gvar) 
    or gvarCaseExprAccs(gvar, invk.getAnArgument().asExpr())) and
  invk.asExpr().getEnclosingStmt() = s) 
}

// don't need to check if the global variable was declared inside the function scope, by definition of being global
predicate fnModifiesGVar(GlobalVariable gvar, Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtModifiesGVar( s, gvar) )
}

predicate fnAccsGVar(GlobalVariable gvar, Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtAccsGVar( s, gvar) )
}

// arg cases
// --------------------------------------------------------------------------------------------------------------------------------------- 

predicate argModifiesRecCase( DataFlow::FunctionNode fctArgNode, AccessPath ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnModifiesRecCase(ap, invk.getACallee())
      or 
      argModifiesRecCase( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or
      recCaseExprMods( ap, invk.asExpr())
      or 
      recCaseExprMods(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argModifiesGVar( DataFlow::FunctionNode fctArgNode, GlobalVariable ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnModifiesGVar(ap, invk.getACallee())
      or 
      argModifiesGVar( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      gvarCaseExprMods(ap, invk.asExpr())
      or 
      gvarCaseExprMods(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argModifiesLocalVar( DataFlow::FunctionNode fctArgNode, LocalVariable ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnModifiesLocalVar(ap, invk.getACallee())
      or 
      argModifiesLocalVar( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      lvarCaseExprMods(ap, invk.asExpr())
      or 
      lvarCaseExprMods(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argModifiesSSAVar( DataFlow::FunctionNode fctArgNode, SsaVariable ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnModifiesSSAVar(ap, invk.getACallee())
      or 
      argModifiesSSAVar( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      ssavarCaseExprMods(ap, invk.asExpr())
      or 
      ssavarCaseExprMods(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argAccessesRecCase( DataFlow::FunctionNode fctArgNode, AccessPath ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnAccsRecCase(ap, invk.getACallee())
      or 
      argAccessesRecCase( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or
      recCaseExprAccs( ap, invk.asExpr())
      or 
      recCaseExprAccs(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argAccessesGVar( DataFlow::FunctionNode fctArgNode, GlobalVariable ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnAccsGVar(ap, invk.getACallee())
      or 
      argAccessesGVar( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      gvarCaseExprAccs(ap, invk.asExpr())
      or 
      gvarCaseExprAccs(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argAccessesLocalVar( DataFlow::FunctionNode fctArgNode, LocalVariable ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnAccsLocalVar(ap, invk.getACallee())
      or 
      argAccessesLocalVar( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      lvarCaseExprAccs(ap, invk.asExpr())
      or 
      lvarCaseExprAccs(ap, invk.getAnArgument().asExpr())
      )
    )
}

predicate argAccessesSSAVar( DataFlow::FunctionNode fctArgNode, SsaVariable ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      fnAccessesSSAVar(ap, invk.getACallee())
      or 
      argAccessesSSAVar( invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      ssavarCaseExprAccs(ap, invk.asExpr())
      or 
      ssavarCaseExprAccs(ap, invk.getAnArgument().asExpr())
      )
    )
}

// recursive case
// --------------------------------------------------------------------------------------------------------------------------------------- MkAccessStep
predicate recCaseDefInTarget(AccessPath ap, Stmt s) {
	ap = MkAccessStep(_, _) and
	exists(VarDef d | d.getTarget() = ap.getAnInstance() and
    d.getTarget().getEnclosingStmt() = s)
}

predicate recCaseExprMods(AccessPath ap, Expr e) {
  ap = MkAccessStep(_, _) and
  exists(VarDef d | d.getTarget() = ap.getAnInstance() and
    d.getTarget().getParentExpr*() = e)
}

predicate recCaseAccInTarget(AccessPath ap, Stmt s) {
	//ap = MkAccessStep(_, _) and // don't need this check, since ap will only be equal to a PropAccess if it's the recursive MkAccessStep case
	exists( PropAccess p | p = ap.getAnInstance() and p.getEnclosingStmt() = s)
}

predicate recCaseExprAccs(AccessPath ap, Expr e) {
  //ap = MkAccessStep(_, _) and // don't need this check, since ap will only be equal to a PropAccess if it's the recursive MkAccessStep case
  exists( PropAccess p | p = ap.getAnInstance() and p.getParentExpr*() = e)
}

predicate stmtModifiesRecCase(Stmt s, AccessPath ap) {
	ap = MkAccessStep(_, _) and inScopeModCaseRecCase(s, ap) 
}

predicate stmtAccsRecCase(Stmt s, AccessPath ap) {
	ap = MkAccessStep(_, _) and inScopeAccCaseRecCase(s, ap) 
}


predicate inScopeModCaseRecCase(Stmt s, AccessPath ap) {
	recCaseDefInTarget(ap, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnModifiesRecCase( ap, invk.getACallee()) 
    or argModifiesRecCase( invk.getAnArgument().(DataFlow::FunctionNode), ap)
    or recCaseExprMods(ap, invk.getAnArgument().asExpr())
    ) and 
  invk.asExpr().getEnclosingStmt() = s) 
}

predicate inScopeAccCaseRecCase(Stmt s, AccessPath ap) {
	recCaseAccInTarget(ap, s)
	or
	exists ( DataFlow::InvokeNode invk |  (fnAccsRecCase( ap, invk.getACallee()) or argAccessesRecCase( invk.getAnArgument().(DataFlow::FunctionNode), ap) 
    or recCaseExprAccs(ap, invk.getAnArgument().asExpr())
    ) and
  invk.asExpr().getEnclosingStmt() = s) 
}

// don't need to check if the global variable was declared inside the function scope, by definition of being global
predicate fnModifiesRecCase(AccessPath ap, Function f) {
	ap = MkAccessStep(_, _) and 
	exists ( Stmt s |  s.getContainer() = f and  stmtModifiesRecCase( s, ap)
    and not baseDefinedLocally(ap, f)  // do we need this, to not count the "this" cases
    )
	//or thisModInFct(ap, f)
}

predicate fnAccsRecCase(AccessPath ap, Function f) {
	ap = MkAccessStep(_, _) and 
	exists ( Stmt s |  s.getContainer() = f and  stmtAccsRecCase( s, ap)
    and not baseDefinedLocally(ap, f)  // do we need this, to not count the "this" cases
    )
	//or thisModInFct(ap, f)
}

predicate baseDefinedLocally(AccessPath ap, Function f) {
	ap.getBase() = MkThisRoot(f.getThisBinder()) or
	exists(LocalVariable lvar | ap.getBase() = MkCapturedRoot(lvar) and lvar.getDeclaringContainer() = f) or
	exists(PurelyLocalVariable lvar | ap.getBase() = MkPurelyLocalNoSSaRoot(lvar) and lvar.getDeclaringContainer() = f) or
	exists(SsaVariable svar | ap.getBase() = MkSsaRoot(svar) and svar.getSourceVariable().getDeclaringContainer() = f)//svar.getAUse().getVariable().(LocalVariable).getDeclaringContainer() = f)
}

LocalVariable baseLocalVar(AccessPath ap, Function f) {
	exists(LocalVariable lvar | ap.getBase() = MkCapturedRoot(lvar) and lvar.getDeclaringContainer() = f and result = lvar) or
	exists(PurelyLocalVariable lvar | ap.getBase() = MkPurelyLocalNoSSaRoot(lvar) and lvar.getDeclaringContainer() = f and result = lvar) or
	exists(SsaVariable svar | ap.getBase() = MkSsaRoot(svar) 
		and result.getDeclaringContainer() = f and result = svar.getSourceVariable())//result = svar.getAUse().getVariable() and result.(LocalVariable).getDeclaringContainer() = f)
}

predicate thisModInFct(AccessPath ap, Function f) {
	ap.getBase() = MkThisRoot(f.getThisBinder()) and
	exists ( Stmt s |  s.getContainer() = f and  stmtModifiesRecCase( s, ap))
}

predicate thisAccInFct(AccessPath ap, Function f) {
	ap.getBase() = MkThisRoot(f.getThisBinder()) and
	exists ( Stmt s |  s.getContainer() = f and  stmtAccsRecCase( s, ap))
}

predicate thisRefInFct( AccessPath ap, Function f) {
	thisModInFct(ap, f) or thisAccInFct(ap, f)
}

predicate localModInFct(AccessPath ap, Function f) {
	baseDefinedLocally(ap, f) and not ap.getBase() = MkThisRoot(f.getThisBinder()) and
	exists ( Stmt s |  s.getContainer() = f and  stmtModifiesRecCase( s, ap))
}

predicate localAccInFct(AccessPath ap, Function f) {
	baseDefinedLocally(ap, f) and not ap.getBase() = MkThisRoot(f.getThisBinder()) and
	exists ( Stmt s |  s.getContainer() = f and  stmtAccsRecCase( s, ap))
}

predicate localRefInFct(AccessPath ap, Function f) {
	localModInFct(ap, f) or localAccInFct(ap, f)
}

predicate stmtModifies( Stmt s, AccessPath ap) {
  exists (SsaVariable svar | stmtModifiesSSAVar(s, svar) and ap = MkSsaRoot(svar))
  or
  exists( GlobalVariable gvar | stmtModifiesGVar(s, gvar) and ap = MkGlobalRoot(gvar))
  or
  exists( LocalVariable lvar | stmtModifiesLocalVar(s, lvar) and (ap = MkCapturedRoot(lvar) or ap = MkPurelyLocalNoSSaRoot(lvar)))
  or
  exists( VarDef d | ap.getAnInstance() = d and
    d.getTarget().getEnclosingStmt() = s)
  or 
  ( stmtModifiesRecCase(s, ap)  and ap = MkAccessStep(_, _))
  or
  exists(Stmt iS | iS.nestedIn(s) and stmtModifies( iS, ap))
  or 
  (exists( AccessPath bap | ap = MkAccessStep(bap, _) and stmtModifies(s, bap)))
  or 
  paramNameStmtMod( s, ap)
  or exists( DataFlow::InvokeNode invk | invk.asExpr().getEnclosingStmt() = s and argStmtMods(invk.getAnArgument().(DataFlow::FunctionNode), ap))
  or exists( DataFlow::InvokeNode invk | invk.asExpr().getEnclosingStmt() = s and stmtModifies(invk.getAnArgument().asExpr().getEnclosingStmt(), ap))
  // this next line assumes assignment to a dynamic property access modifies the base access path (i.e. all properties)
  // UNCOMMENT this line for the conservative analysis
  or exists(AssignExpr ae | ae.getLhs() = ap.(DynamicPropAccessPath).getPropAcc() and ae.getEnclosingStmt() = s) 
}

predicate paramNameStmtMod( Stmt s, AccessPath ap) {
  thisCaseModsPerStmt(s, ap) or localVarModsPerStmt(s, ap)
}

predicate stmtModifiesOrControls( Stmt s, AccessPath ap) {
	stmtModifies( s, ap) or
	( ap.getAnInstance().getParentExpr*() = s.(ControlStmtWithTest).getTest()) // don't need to add the "and stmtAccesses(s, ap)" since this is implied by ap being in the test
}

predicate argStmtAccs( DataFlow::FunctionNode fctArgNode, AccessPath ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr().getParentExpr*() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      argStmtAccs(invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      exists(Stmt s | stmtAccesses(s, ap) and s.getContainer() = invk.getACallee())
      )
    )
  or 
  exists(Stmt s | stmtAccesses(s, ap) and s.getContainer() = fctArgNode.getFunction())
}

predicate argStmtMods( DataFlow::FunctionNode fctArgNode, AccessPath ap) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr().getParentExpr*() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      argStmtMods(invk.getAnArgument().(DataFlow::FunctionNode), ap)
      or 
      exists(Stmt s | stmtModifies(s, ap) and s.getContainer() = invk.getACallee())
      )
    )
  or 
  exists(Stmt s | stmtModifies(s, ap) and s.getContainer() = fctArgNode.getFunction())
}

predicate stmtAccesses( Stmt s, AccessPath ap) {
	exists( SsaVariable svar | stmtAccessesSSAVar( s, svar) and ap = MkSsaRoot(svar)) 
	or
	exists( LocalVariable lvar | stmtAccsLocalVar( s, lvar) and (ap = MkCapturedRoot(lvar) or ap = MkPurelyLocalNoSSaRoot(lvar)))
	or
	exists( GlobalVariable gvar | stmtAccsGVar( s, gvar) and ap = MkGlobalRoot(gvar))
	or 
  ( stmtAccsRecCase(s, ap)  and ap = MkAccessStep(_, _))
  or
  exists(Stmt iS | iS.nestedIn(s) and stmtAccesses( iS, ap))
  or 
  (exists( AccessPath bap | ap = MkAccessStep(bap, _) and stmtAccesses(s, bap)))
  or 
  paramNameStmtAcc( s, ap)
  or exists( DataFlow::InvokeNode invk | invk.asExpr().getEnclosingStmt() = s and argStmtAccs(invk.getAnArgument().(DataFlow::FunctionNode), ap))
  or exists( DataFlow::InvokeNode invk | invk.asExpr().getEnclosingStmt() = s and stmtAccesses(invk.getAnArgument().asExpr().getEnclosingStmt(), ap))
}

predicate paramNameStmtAcc( Stmt s, AccessPath ap) {
  thisCaseAccsPerStmt(s, ap) or localVarAccsPerStmt(s, ap)
}

predicate stmtReferences(Stmt s, AccessPath ap) {
	(stmtAccesses(s, ap) or stmtModifiesOrControls(s, ap)) and isLocal(ap) 
}

predicate isLocal(AccessPath ap) {
	not ap.getAnInstance().getFile().toString().regexpMatch(".*tools.*")
	and 
	not ap.getAnInstance().getFile().toString().regexpMatch(".*package.*")
}

predicate stmtsBothModify(Stmt s1, Stmt s2, AccessPath ap) {
	stmtModifiesOrControls(s1, ap) and stmtModifiesOrControls(s2, ap)
}

predicate stmtsCanSwap(Stmt s1, Stmt s2) {
	exists(BlockStmt b | s1 = b.getAStmt() and s2 = b.getAStmt()) and 
	forall(AccessPath ap | stmtModifiesOrControls(s1, ap) | not stmtReferences(s2, ap))
	and
	forall(AccessPath ap | stmtModifiesOrControls(s2, ap) | not stmtReferences(s1, ap))
	and 
	forall(AccessPath ap | stmtAccesses(s1, ap) | not stmtModifiesOrControls(s2, ap))
	and 
	forall(AccessPath ap | stmtAccesses(s2, ap) | not stmtModifiesOrControls(s1, ap))
	and 
	not stmtsConflictingSideEffects( s1, s2)
	and
	not (stmtHasGlobalSideEffects(s1) or stmtHasGlobalSideEffects(s2))
  and (not s1 instanceof ReturnStmt)
  and (not s2 instanceof ReturnStmt)
  //not exists(StmtLocalAccessPath ap | ap.getScopeStmt() = s1 and stmtsBothModify(s1, s2, ap))
}

predicate stmtsConflictingSideEffects( Stmt s1, Stmt s2) {
	s1.(IODependentStmt).getPackage() = s2.(IODependentStmt).getPackage() 
	and
	( stmtHasSideEffectsForPkg(s1.(IODependentStmt)) or stmtHasSideEffectsForPkg(s2.(IODependentStmt))) 
}

// predicate that determines if 2 statements are consecutive in the same BlockStmt, which is what we're using for scope essentially
predicate consecutive( Stmt fst, Stmt snd) {    
  exists( BlockStmt b, int i | fst = b.getStmt( i) and snd = b.getStmt( i + 1)  )
}

// check if we can swap s with the earlier statement (to swap, must be able to swap with all statements in between too)
predicate stmtCanSwapUpTo( Stmt s, Stmt earlier) {  
  s = earlier  
  or  
  exists( Stmt mid | stmtCanSwapUpTo( s, mid) and consecutive( earlier, mid) and stmtsCanSwap( s, earlier))
}

// same as stmtCanSwapUpTo, but checks if can swap down
predicate stmtCanSwapDownTo( Stmt s, Stmt later) {  
  s = later  
  or  
  exists( Stmt mid | stmtCanSwapDownTo( s, mid) and consecutive( mid, later) and stmtsCanSwap( s, later))
}

predicate stmtsInSameBlockStmt(Stmt s1, Stmt s2) {
	exists(BlockStmt b | b.getAStmt() = s1 and b.getAStmt() = s2)
}

// get the earliest statement s can swap with
Stmt stmtEarliestStmtToSwapWith( Stmt s) {  
  result = min( Stmt earlier | stmtsInSameBlockStmt(s, earlier) and stmtCanSwapUpTo( s, earlier) | earlier order by earlier.getLocation().getStartLine())
}

// get the latest statement s can swap with
Stmt stmtLatestStmtToSwapWith( Stmt s) {  
  result = max( Stmt later | stmtsInSameBlockStmt(s, later) and stmtCanSwapDownTo( s, later) | later order by later.getLocation().getStartLine())
}



// query predicates, get list of properties we care about
// mostly for debugging

predicate thisCaseModsPerStmt(Stmt s, AccessPath ap) {
	exists(ThisModAccessPath tap | tap.isRefdByStmt(s) and tap.pathEquals(ap) and not ap.getBase() = MkThisRoot(_))
}

predicate thisCaseAccsPerStmt(Stmt s, AccessPath ap) {
	exists(ThisAccAccessPath tap | tap.isRefdByStmt(s) and tap.pathEquals(ap) and not ap.getBase() = MkThisRoot(_))
}

predicate localVarModsPerStmt(Stmt s, AccessPath ap) {
	exists( ParamModAccessPath pmap | pmap.isRefdByStmt(s) and pmap.pathEquals(ap) and not ap.getBase() = MkThisRoot(_) and not ap = pmap) //and s.getFile().toString().regexpMatch(".*args.*")
}

predicate localVarAccsPerStmt(Stmt s, AccessPath ap) {
	exists( ParamAccAccessPath pmap | pmap.isRefdByStmt(s) and pmap.pathEquals(ap) and not ap.getBase() = MkThisRoot(_) and not ap = pmap) //and s.getFile().toString().regexpMatch(".*args.*")
}

predicate inLocalSrcFile(Stmt s) {
	s.getFile().toString().regexpMatch(".*input/async-.*")
}

AccessPath getAnAccAP(Stmt s) {
	isLocal(result) and (stmtAccesses( s, result) or thisCaseAccsPerStmt(s, result) or localVarAccsPerStmt(s, result))
}

AccessPath getAModAP(Stmt s) {
	isLocal(result) and (stmtModifiesOrControls(s, result) or thisCaseModsPerStmt(s, result) or localVarModsPerStmt(s, result))	
}


bindingset[pkg]
IOModuleString getIOPortalPackage(string pkg) {
	pkg.matches("%(root https://www.npmjs.com/package/fs%") and result = "fs" or // note: this includes fs-extra, fs-admin
	pkg.matches("%(root https://www.npmjs.com/package/readable-fs%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/graceful-fs%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/mock-fs%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/cspell-io%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/jsdoc%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/path%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/zlib%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/io%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/tmp%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/rimraf%") and result = "fs" or 
  pkg.matches("%(root https://www.npmjs.com/package/http%") and result = "http" or // this includes https and http2
  // pkg.matches("%(root https://www.npmjs.com/package/fetch%") and result = "fetch" or 
  pkg.matches("%(root https://www.npmjs.com/package/sequelize%") and result = "db" or
  pkg.matches("%(root https://www.npmjs.com/package/redis%") and result = "db" or
  pkg.matches("%(root https://www.npmjs.com/package/mongoose%") and result = "db" or
  pkg.matches("%(root https://www.npmjs.com/package/pg%") and result = "db" or 
  pkg.matches("%(root https://www.npmjs.com/package/mime-db%") and result = "db" or
  pkg.matches("%(root https://www.npmjs.com/package/firebase%") and result = "db" or 
  pkg.matches("%(root https://www.npmjs.com/package/sqlite3%") and result = "db" or
  pkg.matches("%(root https://www.npmjs.com/package/express%") and result = "http" or 
  pkg.matches("%(root https://www.npmjs.com/package/socks%") and result = "http" or 
  pkg.matches("%(root https://www.npmjs.com/package/puppeteer%") and result = "http"
}

class IOModuleString extends string {
	IOModuleString() {
		this = "fs" or
		this = "fetch" or
		this = "http" or
    this = "db"
  }
}

// class to represent statements that are dependent on IO
// we define this as being statements which contain a call to a function which originated from an IO-dependent portal 
class IODependentStmt extends Stmt {
	IOModuleString pkg;

	IODependentStmt() {
		stmtDependsOnIOModule(this, pkg)
    or
    stmtSideEffectDependsOnPkg( this, pkg)
  }	

  string getPackage() {
    result = pkg
  }
}

predicate callIsExitNodeOfPkg( IOModuleString pkgName, DataFlow::InvokeNode invk) {
	exists( Portal p | getIOPortalPackage( p.toString()) = pkgName and invk = p.getAnExitNode(_).(DataFlow::InvokeNode))
}

predicate recursiveDependsOnIOModule( IOModuleString ioModPackage, DataFlow::InvokeNode invk) {
	exists( Stmt innerS | 
    innerS.getContainer() = invk.getACallee() 
    and stmtDependsOnIOModule( innerS, ioModPackage)
    )	
  or
  exists(DataFlow::InvokeNode innerF | innerF.asExpr().getParentExpr*() = invk.getACallee().getBody() and 
    (callIsExitNodeOfPkg( ioModPackage, innerF) or recursiveDependsOnIOModule( ioModPackage, innerF) ))

}

predicate nestedDependsOnIOModule( IOModuleString ioModPackage, Stmt outerS) {
  exists( Stmt innerS | innerS.nestedIn(outerS) and stmtDependsOnIOModule(innerS, ioModPackage))
}

predicate stmtDependsOnIOModule( Stmt s, IOModuleString ioModPackage) {
	exists( DataFlow::InvokeNode invk | 
		invk.asExpr().getEnclosingStmt() = s 
		and 
		(
			callIsExitNodeOfPkg( ioModPackage, invk) // base case 
			or
			recursiveDependsOnIOModule( ioModPackage, invk) // recursive caase
      or 
      argDependsOnIOModule( invk.getAnArgument().(DataFlow::FunctionNode), ioModPackage)
      or 
      exprDependsOnIOModule(invk.getAnArgument().asExpr(), ioModPackage)
      )
   ) 
  or nestedDependsOnIOModule( ioModPackage, s)
}

predicate exprDependsOnIOModule( Expr e, IOModuleString pkg) {
  exists(DataFlow::InvokeNode invk | invk.asExpr().getParentExpr*() = e and 
    (recursiveDependsOnIOModule( pkg, invk) or callIsExitNodeOfPkg(pkg, invk)))
}

predicate argDependsOnIOModule( DataFlow::FunctionNode fctArgNode, IOModuleString pkg) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr().getParentExpr*() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      callIsExitNodeOfPkg( pkg, invk)
      or 
      recursiveDependsOnIOModule( pkg, invk)
      or 
      argHasPkgSideEffect( invk.getAnArgument().(DataFlow::FunctionNode), pkg)
      )
    )
}


bindingset[calleeName]
predicate isSideEffectName( string calleeName, IOModuleString pkg) {
	pkg = "fs" and calleeName.matches("%write%")
  or
  pkg = "fs" and calleeName.matches("%append%")
  or
  pkg = "fs" and calleeName.matches("%unlink%")
  or
  pkg = "fs" and calleeName.matches("%rename%")
  or
  pkg = "fs" and calleeName.matches("%copy%")
  or
  pkg = "fs" and calleeName.matches("%mkdir%")
  or
  pkg = "fs" and calleeName.matches("%remove%")
  or
  pkg = "fs" and calleeName.matches("%rmdir%")
  or
  pkg = "fs" and calleeName.matches("move")
  or
  pkg = "fs" and calleeName.matches("output%") // outputFile, outputFileSync, etc (in fs-extra)
  or
  // these next are for the tmp package
  pkg = "fs" and calleeName.matches("dir")
  or
  pkg = "fs" and calleeName.matches("file")
  or
  pkg = "fs" and calleeName.matches("dirSync")
  or
  pkg = "fs" and calleeName.matches("fileSync")
  // http side effects 
  or 
  pkg = "http" and calleeName.matches("start")
  or 
  pkg = "http" and calleeName.matches("stop")
  or 
  pkg = "http" and calleeName = "goto"
}

bindingset[calleeName]
predicate isGlobalSideEffectName( string calleeName) {
	calleeName.matches("exec%") or
  calleeName.matches("%eval") or 
  calleeName = "evaluate" or 
  calleeName = "setTimeout" or 
  calleeName = "wait" or 
  calleeName = "run" or 
  calleeName = "spawn" or
  calleeName = "fork" or 
  calleeName = "snapSpawn" or // jest
  calleeName = "goto" 
}

predicate isBuiltinSideEffect( IOModuleString pkgName, DataFlow::InvokeNode invk) {
  invk.getCalleeName() = "chdir" and pkgName = "fs" // process.chdir
  // http side effects
  or
  pkgName = "http" and invk.getCalleeName().matches("start%")
  or 
  pkgName = "http" and invk.getCalleeName().matches("stop%")
  or 
  pkgName = "http" and invk.getCalleeName() = "load"
  or 
  pkgName = "http" and invk.getCalleeName() = "launch"
}

predicate callIsSideEffectOfPkg( IOModuleString pkgName, DataFlow::InvokeNode invk) {
	exists( Portal p | getIOPortalPackage( p.toString()) = pkgName 
    and invk = p.getAnExitNode(_).(DataFlow::InvokeNode)
    and isSideEffectName(invk.getCalleeName(), pkgName)
    )
 or isBuiltinSideEffect( pkgName, invk)
}

predicate nestedHasSideEffetForPkg( IODependentStmt outerS) {
  exists( IODependentStmt innerS | innerS.nestedIn(outerS) and stmtHasSideEffectsForPkg(innerS))
}

predicate nestedHasSideEffetForPkgDependency( Stmt outerS, IOModuleString pkg) {
  exists( Stmt innerS | innerS.nestedIn(outerS) and stmtSideEffectDependsOnPkg(innerS, pkg))
}

predicate nestedHasGlobalSideEffects( Stmt outerS) {
  exists( Stmt innerS | innerS.nestedIn(outerS) and stmtHasGlobalSideEffects( innerS))
}

// new edge case: if we have a function where the return is an expr 
// (i.e. an arrow function), and it could be a function call, and it could have side effects 
// running into this in core-test.ts in desktop/desktop
predicate argHasGlobalSideEffect( DataFlow::FunctionNode fctArgNode) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr().getParentExpr*() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      isGlobalSideEffectName( invk.getCalleeName())
      or 
      fctHasGlobalSideEffectsForPkg( invk.getACallee())
      or
      testGlobalSideEffect( invk)
      or 
      argHasGlobalSideEffect( invk.getAnArgument().(DataFlow::FunctionNode))
      )
    )
}

predicate argHasPkgSideEffect( DataFlow::FunctionNode fctArgNode, IOModuleString pkg) {
  exists( DataFlow::InvokeNode invk | 
    ( invk.asExpr().getParentExpr*() = fctArgNode.getFunction().getBody()
      or
      invk.asExpr().getEnclosingStmt() = fctArgNode.getFunction().getABodyStmt() 
      )
    and 
    (
      callIsSideEffectOfPkg( pkg, invk)
      or 
      fctHasSideEffectsForPkg( invk.getACallee(), pkg)
      or 
      argHasPkgSideEffect( invk.getAnArgument().(DataFlow::FunctionNode), pkg)
      )
    )
}

// running into issues with tests and swapping past expect
predicate testGlobalSideEffect( DataFlow::InvokeNode invk) {
  (invk.getCalleeName().matches("toHaveBeenCalled%") or invk.getCalleeName().matches("toMatchSnapshot") or invk.getCalleeName().matches("toBe%"))// this also matches "toHaveBeenCalledTimes"  
  and 
  exists( DataFlow::InvokeNode rec | invk.(DataFlow::MethodCallNode).getReceiver() = rec and rec.getCalleeName() = "expect")
  or 
  invk.(DataFlow::MethodCallNode).getReceiver().asExpr().getAChildExpr*().(TypeAssertion).getTypeAnnotation().toString().matches("jest%")
  or 
  exists( PropAccess pa | invk.(DataFlow::MethodCallNode).getReceiver().asExpr() = pa and pa.getPropertyName() = "to" and 
    exists( DataFlow::InvokeNode rec | pa.getBase() = rec.asExpr() and rec.getCalleeName() = "expect"))
  or 
  exists( PropAccess pa | invk.(DataFlow::MethodCallNode).getReceiver().asExpr() = pa and pa.getPropertyName() = "be" and pa.getBase().(PropAccess).getPropertyName() = "to" and 
    exists( DataFlow::InvokeNode rec | pa.getBase().(PropAccess).getBase() = rec.asExpr() and rec.getCalleeName() = "expect"))
  or invk.getCalleeName().matches("received") // mainly for tests: IExpressServerFacade
  and invk.(DataFlow::MethodCallNode).getReceiver().toString().matches("%Mock%") // heuristic: variable name
  or (invk.getCalleeName() = "equal" or invk.getCalleeName().matches("%Equal%") or invk.getCalleeName() = "ok" or invk.getCalleeName() = "true" or invk.getCalleeName() = "is" )
  and (invk.(DataFlow::MethodCallNode).getReceiver().toString().matches("assert") or invk.(DataFlow::MethodCallNode).getReceiver().toString().matches("t")) // heuristic: variable name
  or exists(DataFlow::InvokeNode rec | rec.getCalleeName() = "assert" and invk.asExpr().getParentExpr*() = rec.getAnArgument().asExpr()) 
}

Function getEnclosingFunction(Stmt s) {
  result = s.getContainer()
  or 
  result = s.getContainer().getEnclosingContainer*()
}

predicate functionIsParameter(DataFlow::InvokeNode invk) {
  exists( Function f | f = getEnclosingFunction(invk.asExpr().getEnclosingStmt()) 
    and exists(f.getParameterByName(invk.getCalleeName()))
    )
}

predicate stmtHasGlobalSideEffects(Stmt s) {
	exists( DataFlow::InvokeNode invk | 
   invk.asExpr().getParentExpr*().getEnclosingStmt() = s 
   and
   (
    isGlobalSideEffectName( invk.getCalleeName())
    or 
    fctHasGlobalSideEffectsForPkg( invk.getACallee())
    or 
    argHasGlobalSideEffect( invk.getAnArgument().(DataFlow::FunctionNode))
    or
    testGlobalSideEffect( invk)
    or 
    functionIsParameter(invk)
    or 
    exprHasGlobalSideEffect(invk.getAnArgument().asExpr())
    // IF CONSERVATIVE ANALYSIS UNCOMMENT OUT THE FOLLOWING CONDITION
    // or 
    // not exists(invk.getACallee())
    )
   )
  or nestedHasGlobalSideEffects( s)
}

predicate fctHasGlobalSideEffectsForPkg( Function f) {
	exists( Stmt s | s.getContainer() = f and stmtHasGlobalSideEffects( s))
  or
  exists(DataFlow::InvokeNode invk | invk.asExpr().getParentExpr*() = f.getBody() and 
    (fctHasGlobalSideEffectsForPkg(invk.getACallee()) or isGlobalSideEffectName(invk.getCalleeName())))
}

predicate exprHasGlobalSideEffect( Expr e){
  exists(DataFlow::InvokeNode invk | invk.asExpr().getParentExpr*() = e and 
    (fctHasGlobalSideEffectsForPkg( invk.getACallee()) or isGlobalSideEffectName( invk.getCalleeName())))
}

predicate exprHasSideEffectForPkg( Expr e, IOModuleString pkg) {
  exists(DataFlow::InvokeNode invk | invk.asExpr().getParentExpr*() = e and 
    (fctHasSideEffectsForPkg(invk.getACallee(), pkg) or callIsSideEffectOfPkg(pkg, invk)))
}

predicate stmtSideEffectDependsOnPkg( Stmt s, IOModuleString pkg) {
  exists( DataFlow::InvokeNode invk | 
    invk.asExpr().getParentExpr*().getEnclosingStmt() = s 
    and
    (
      callIsSideEffectOfPkg( pkg, invk)
      or 
      fctHasSideEffectsForPkg( invk.getACallee(), pkg)
      or 
      argHasPkgSideEffect( invk.getAnArgument().(DataFlow::FunctionNode), pkg)
      or 
      exprHasSideEffectForPkg(invk.getAnArgument().asExpr(), pkg)
      )
    )
  or nestedHasSideEffetForPkgDependency( s, pkg)
}

predicate stmtHasSideEffectsForPkg( IODependentStmt s) {
	exists( DataFlow::InvokeNode invk | 
   invk.asExpr().getParentExpr*().getEnclosingStmt() = s 
   and
   (
    callIsSideEffectOfPkg( s.getPackage(), invk)
    or 
    fctHasSideEffectsForPkg( invk.getACallee(), s.getPackage())
    or 
    argHasPkgSideEffect( invk.getAnArgument().(DataFlow::FunctionNode), s.getPackage())
    or 
    exprHasSideEffectForPkg(invk.getAnArgument().asExpr(), s.getPackage())
    )
   )
  or nestedHasSideEffetForPkg( s)
}

predicate fctHasSideEffectsForPkg( Function f, IOModuleString pkg) {
	exists( IODependentStmt s | s.getContainer() = f and stmtHasSideEffectsForPkg( s) and s.getPackage() = pkg)
  or
  exists(DataFlow::InvokeNode invk | invk.asExpr().getParentExpr*() = f.getBody() and 
    (fctHasSideEffectsForPkg(invk.getACallee(), pkg) or callIsSideEffectOfPkg(pkg, invk)))
}

bindingset[name]
predicate nameIsIO(string name) {
	name = "fetch" or
	name = "readFile" or 
	name = "writeFile" or
	name = "mkdir"
	// anything coming from fs or http modules
}

predicate stmtDependsOnIO(Stmt s) {
	exists( DataFlow::InvokeNode invk | 
    invk.asExpr().getEnclosingStmt() = s and
    (   nameIsIO( invk.getCalleeName()) // do we want to track portals?
     or 
     fnDependsOnIO( invk.getACallee()))
    )
}

predicate fnDependsOnIO(Function f) {
	exists ( Stmt s |  s.getContainer() = f and  stmtDependsOnIO( s) )
}

predicate stmtInLoop(Stmt s) {
	exists(LoopStmt l | s.getParentStmt+() = l)
}

predicate stmtHasAwait(Stmt s) {
	exists( SwappableAwaitExpr ae | ae.getEnclosingStmt().getParentStmt*() = s)
}

predicate fnHasAwait(Function f) {
	exists(Stmt s | s.getContainer() = f and stmtHasAwait(s))
}



predicate importIsIOModule(Import imp) {
	exists( string s | 
		(s = "http" or s = "fs" or s = "fetch") and
		imp.getImportedPath().getBaseName() = s
    )
}

class AsyncFunction extends Function {
  AsyncFunction() {
    this.isAsync()
  }
}

string getStringRepStmt( Stmt s) { 
  result = s.getLocation().getStartLine() + ", " + s.getLocation().getStartColumn() + ", " + 
  s.getLocation().getEndLine() + ", " + s.getLocation().getEndColumn()
}


