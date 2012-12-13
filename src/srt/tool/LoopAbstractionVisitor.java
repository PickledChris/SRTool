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
        List<Stmt> stmts = new LinkedList<Stmt>();

        if (exprs.size() > 0) {

            Expr invariant = getInvariantExpr(exprs);

            // assert invariant
            Stmt entry = new AssertStmt(invariant);

            // havoc invariant
            Stmt havoc = new BlockStmt(getHavocStatements(exprs));

            // assume invariant
            Stmt assume = new AssumeStmt(invariant);
            stmts.add(entry); stmts.add(havoc); stmts.add(assume);


            stmts.add(ifBlockBuilder(whileStmt, invariant));

            BlockStmt block = new BlockStmt(stmts);

            return super.visit(block);

        } else {
            return super.visit(whileStmt);
        }
	}

    private Expr getInvariantExpr(List<Expr> exprs) {
        // expr && expr = expr, just vaguely more inefficient

        if (exprs.size() == 1)
            return exprs.get(0);

        else {
            Expr invariant = exprs.get(0);

            for(int i = 1; i < exprs.size(); i++) {
                Expr e = exprs.get(i);
                invariant = new BinaryExpr(BinaryExpr.LAND,invariant,e);
            }
            return invariant;
        }
    }

    private List<Stmt> getHavocStatements(List<Expr> invariant) {
        List<Stmt> list = new LinkedList<Stmt>();

        for (Expr e: invariant) {
            if (e instanceof DeclRef)
                list.add(new HavocStmt((DeclRef) e));
        }
        return list;
    }


    private Stmt ifBlockBuilder(WhileStmt whileStmt, Expr invariant) {
        // Inside block now
        List<Stmt> block = new LinkedList<Stmt>();

        block.add(whileStmt.getBody());

        // assert invariant
        block.add(new AssertStmt(invariant));

        // assume false
        block.add(new AssumeStmt(new IntLiteral(0)));

        // if statement
        return new IfStmt(whileStmt.getCondition(),
                new BlockStmt(block),
                null);
    }
}
