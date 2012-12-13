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

        final List<Expr> exprs = whileStmt.getInvariantList().getExprs();
        final List<Stmt> stmts = new LinkedList<Stmt>();

        if (!exprs.isEmpty()) {

            final Expr invariant = getInvariantExpr(exprs);

            // assert invariant
            final Stmt entry = new AssertStmt(invariant);

            // havoc invariant
            final Stmt havoc = new BlockStmt(getHavocStatements(exprs));

            // assume invariant
            final Stmt assume = new AssumeStmt(invariant);
            stmts.add(entry); stmts.add(havoc); stmts.add(assume);


            stmts.add(ifBlockBuilder(whileStmt, invariant));

            final BlockStmt block = new BlockStmt(stmts);

            return visit(block);

        } else {
            return super.visit(whileStmt);
        }
	}

    private static Expr getInvariantExpr(final List<Expr> exprs) {
        // expr && expr = expr, just vaguely more inefficient

        if (1 == exprs.size()) {
            return exprs.get(0);
        } else {
            Expr invariant = exprs.get(0);

            for(int i = 1; i < exprs.size(); i++) {
                invariant = new BinaryExpr(BinaryExpr.LAND,invariant,exprs.get(i));
            }
            return invariant;
        }
    }

    private static List<Stmt> getHavocStatements(final Iterable<Expr> invariant) {
        final List<Stmt> list = new LinkedList<Stmt>();

        for (final Expr e: invariant) {
            if (e instanceof DeclRef) {
                list.add(new HavocStmt((DeclRef) e));
            }
        }
        return list;
    }


    private static Stmt ifBlockBuilder(final WhileStmt whileStmt, final Expr invariant) {
        // Inside block now
        final List<Stmt> block = new LinkedList<Stmt>();

        block.add(whileStmt.getBody());

        // assert invariant
        block.add(new AssertStmt(invariant));

        // assume false
        block.add(new AssumeStmt(new IntLiteral(0)));

        // if statement
        return new IfStmt(whileStmt.getCondition(),
                new BlockStmt(block),
                new BlockStmt(new LinkedList<Stmt>()));
    }
}
