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
import srt.ast.IntLiteral;
import srt.ast.Stmt;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class PredicationVisitor extends DefaultVisitor {

	public PredicationVisitor() {
		super(true);
	}

	private Expr predicate = new IntLiteral(1);
	private int predicateCount = 0;
	private Expr globalPredicateValue = new IntLiteral(1);

	@Override
	public Object visit(IfStmt ifStmt) {

		Expr oldPredicate = this.predicate;
		DeclRef thenPredicate = getNextPredicate();
		DeclRef elsePredicate = getNextPredicate();

		AssignStmt thenCondition = new AssignStmt(thenPredicate,
				new BinaryExpr(BinaryExpr.LAND, this.predicate, ifStmt.getCondition()));
		AssignStmt elseCondition = new AssignStmt(elsePredicate,
				new BinaryExpr(BinaryExpr.LAND, this.predicate, new UnaryExpr(UnaryExpr.LNOT, ifStmt.getCondition())));


        this.predicate = thenPredicate;
		Stmt thenStatement = (Stmt) visit(ifStmt.getThenStmt());

        this.predicate = elsePredicate;
		Stmt elseStatement = (Stmt) visit(ifStmt.getElseStmt());

        this.predicate = oldPredicate;

		List<Stmt> list = new ArrayList<Stmt>(4);
		list.add(thenCondition);
		list.add(elseCondition);
		list.add(thenStatement);
		list.add(elseStatement);
		return new BlockStmt(list);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {

		// assert(expr) becomes assert((G && P)  => expr)
        return new AssertStmt(implies(andGlobal(this.predicate), assertStmt.getCondition()), assertStmt);
	}

	@Override
	public Object visit(AssignStmt assignment) {
		// x = E becomes x = ((G && P)  ? E : x)
		TernaryExpr ternaryExpr = new TernaryExpr(andGlobal(this.predicate), assignment.getRhs(), assignment.getLhs());
		return new AssignStmt(assignment.getLhs(), ternaryExpr , assignment);
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
		// assume(expr) becomes A = (G && P ) => expr
		DeclRef newPredicate = getNextPredicate();
		Expr implies =  implies(andGlobal(this.predicate), assumeStmt.getCondition());
		AssignStmt newAssign = new AssignStmt(newPredicate, implies, assumeStmt);
		//G = G && A
        this.globalPredicateValue = new BinaryExpr(BinaryExpr.LAND, this.globalPredicateValue, newPredicate);

		return newAssign;
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
		TernaryExpr ternaryExpr = new TernaryExpr(andGlobal(this.predicate), getNextPredicate(), havocStmt.getVariable());
		return new AssignStmt(havocStmt.getVariable(), ternaryExpr, havocStmt);
	}

	private DeclRef getNextPredicate() {
        this.predicateCount++;
		return new DeclRef(String.format("$P%s", this.predicateCount));
	}

	private static Expr implies(Expr lhs, Expr rhs) {
		return new BinaryExpr(BinaryExpr.LOR, new UnaryExpr(UnaryExpr.LNOT, lhs) ,rhs);
	}

	private Expr andGlobal(Expr expr) {
		return new BinaryExpr(BinaryExpr.LAND, this.globalPredicateValue, expr);
	}

}
