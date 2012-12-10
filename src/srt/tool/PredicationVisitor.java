package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BinaryExpr;
import srt.ast.BlockStmt;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.Stmt;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class PredicationVisitor extends DefaultVisitor {

	public PredicationVisitor() {
		super(true);
	}
	
	private String predicate = "True";
	private int predicateCount = 0;
	private String globalPredicate = "$G";
	private Expr globalPredicateValue = new DeclRef("True");
	
	@Override
	public Object visit(IfStmt ifStmt) {
		
		String oldPredicate = predicate;
		DeclRef thenPredicate = getNextPredicate();
		DeclRef elsePredicate = getNextPredicate();
		
		AssignStmt thenCondition = new AssignStmt(thenPredicate, 
				new BinaryExpr(BinaryExpr.LAND, new DeclRef(predicate), ifStmt.getCondition()));
		AssignStmt elseCondition = new AssignStmt(elsePredicate, 
				new BinaryExpr(BinaryExpr.LAND, new DeclRef(predicate), new UnaryExpr(UnaryExpr.LNOT, ifStmt.getCondition())));
		
		
		predicate = thenPredicate.getName();
		Stmt thenStatement = (Stmt) visit(ifStmt.getThenStmt());
		
		predicate = elsePredicate.getName();
		Stmt elseStatement = (Stmt) visit(ifStmt.getElseStmt());
		
		predicate = oldPredicate;
		
		List<Stmt> list = new ArrayList<Stmt>();
		list.add(thenCondition);
		list.add(elseCondition);
		list.add(thenStatement);
		list.add(elseStatement);
		return new BlockStmt(list);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
		
		// assert(expr) becomes assert((G && P)  => expr)
		AssertStmt newAssert = new AssertStmt(implies(andGlobal(new DeclRef(predicate)), assertStmt.getCondition()), assertStmt);
		return newAssert;
	}

	@Override
	public Object visit(AssignStmt assignment) {
		// x = E becomes x = ((G && P)  ? E : x)
		TernaryExpr ternaryExpr = new TernaryExpr(andGlobal(new DeclRef(predicate)), assignment.getRhs(), assignment.getLhs());
		AssignStmt newAssign = new AssignStmt(assignment.getLhs(), ternaryExpr , assignment);
		return newAssign;
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
		// assume(expr) becomes A = (G && P ) => expr

		DeclRef newPredicate = getNextPredicate();
		Expr implies =  implies(andGlobal(new DeclRef(predicate)), assumeStmt.getCondition());
		AssignStmt newAssign = new AssignStmt(newPredicate, implies, assumeStmt);
		//G = G && A
		globalPredicateValue = new BinaryExpr(BinaryExpr.LAND, globalPredicateValue, newPredicate);
		
		return newAssign;
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
		TernaryExpr ternaryExpr = new TernaryExpr(andGlobal(new DeclRef(predicate)), getNextPredicate(), havocStmt.getVariable());
		AssignStmt newAssign = new AssignStmt(havocStmt.getVariable(), ternaryExpr, havocStmt);
		return newAssign;
	}
	
	private DeclRef getNextPredicate() {
		predicateCount++;
		return new DeclRef(String.format("$P%s", predicateCount));
	}
	
	private Expr implies(Expr lhs, Expr rhs) {
		return new BinaryExpr(BinaryExpr.LOR, new UnaryExpr(UnaryExpr.LNOT, lhs) ,rhs);
	}
	
	private Expr andGlobal(Expr expr) {
		return new BinaryExpr(BinaryExpr.LAND, new DeclRef(globalPredicate), expr);
	}

}
