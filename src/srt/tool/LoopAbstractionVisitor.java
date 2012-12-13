package srt.tool;

import srt.ast.*;
import srt.ast.visitor.impl.DefaultVisitor;

import java.util.LinkedList;
import java.util.List;

public class LoopAbstractionVisitor extends DefaultVisitor {

	public LoopAbstractionVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {

        List<Expr> exprs = whileStmt.getInvariantList().getExprs();
        int length = exprs.size();

        Expr cond;

        if (length > 0) {
            // expr && expr = expr, just vaguely more inefficient
            cond = exprs.get(0);

            for(Expr e : exprs)
                cond = new BinaryExpr(BinaryExpr.LAND,cond,e);
        }
        else {
            return super.visit(whileStmt);
        }

        Expr condition = new BinaryExpr(BinaryExpr.LAND,whileStmt.getCondition(),cond);

		return super.visit(new WhileStmt(condition,whileStmt.getBound(),whileStmt.getInvariantList(),whileStmt.getBody()));
	}

}
