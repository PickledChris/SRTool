package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.ArrayList;
import java.util.List;

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

        IntLiteral bound = whileStmt.getBound();

        // unroll once.
        Expr condition = whileStmt.getCondition();
        Stmt body = whileStmt.getBody();

        Stmt ifStmt = whileVerificationStmt(condition);
        // start for at 1 because one unroll already done
        for(int i = 0; i < bound.getValue(); i++) {

            // use body + the ifStatement generated previously to make up the next body
            List<Stmt> unrolledIfBody = new ArrayList<Stmt>();
            unrolledIfBody.add(body);
            unrolledIfBody.add(ifStmt);
            StmtList newIfBody = new StmtList(unrolledIfBody);

            ifStmt = new IfStmt(condition, new BlockStmt(newIfBody), new EmptyStmt());


        }

		return super.visit(ifStmt);
	}

    private Stmt whileVerificationStmt(Expr condition) {
        List<Stmt> assumeAssert = new ArrayList<Stmt>();
        assumeAssert.add(new AssertStmt(negate(condition)));
        assumeAssert.add(new AssumeStmt(negate(condition)));
        StmtList list = new StmtList(assumeAssert);
        return new BlockStmt(list);
    }

    private Expr negate(Expr expr) {
        Expr expression = new UnaryExpr(UnaryExpr.LNOT, expr);
        return expr;  //To change body of created methods use File | Settings | File Templates.
    }
}
