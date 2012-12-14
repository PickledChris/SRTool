package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.EmptyStmt;
import srt.ast.Expr;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Stmt;
import srt.ast.StmtList;
import srt.ast.UnaryExpr;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopUnwinderVisitor extends DefaultVisitor {

	private boolean unwindingAssertions;
	private int defaultUnwindBound;

	public LoopUnwinderVisitor(boolean unwindingAssertions,
			int defaultUnwindBound) {
		super(true);
		this.unwindingAssertions = unwindingAssertions;
		this.defaultUnwindBound = defaultUnwindBound;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		
		// List that contains preconditions and if statement
		List<Stmt> stmtList = new ArrayList<Stmt>();
		
		// Assert the preconditions
		for (Expr expression : whileStmt.getInvariantList().getExprs()) {
			stmtList.add(new AssertStmt(expression));
		}
		
		int bound;
		if (whileStmt.getBound() == null) {
			bound = defaultUnwindBound;
		} else {
			bound = whileStmt.getBound().getValue();
		}
		
		// If we aren't unrolling any further, replace the while loop with another 
		if (bound == 0) {
			return getVerificationCondition(whileStmt.getCondition());
		}
		
		// Otherwise, unroll once and add in a decremented while loop.
		WhileStmt newWhileStmt = new WhileStmt(whileStmt.getCondition(), new IntLiteral(bound - 1), whileStmt.getInvariantList(), whileStmt.getBody());
		
		List<Stmt> list = new ArrayList<Stmt>();
		list.add(whileStmt.getBody());
		list.add(newWhileStmt);
		IfStmt ifStatement = new IfStmt(whileStmt.getCondition(), new BlockStmt(new StmtList(list)) , new EmptyStmt());
		stmtList.add(ifStatement);
		
		return super.visit(new BlockStmt(new StmtList(stmtList)));
	}

	// Creates the assume and assert statements, based on the soundness parameter passed in.
	private Stmt getVerificationCondition(Expr condition) {
		List<Stmt> list = new ArrayList<Stmt>();
		if (unwindingAssertions) {
			list.add(new AssertStmt(negated(condition)));
		}
		list.add(new AssumeStmt(negated(condition)));
		return new BlockStmt(new StmtList(list));
	}

	private Expr negated(Expr condition) {
		return new UnaryExpr(UnaryExpr.LNOT, condition);
	}

}