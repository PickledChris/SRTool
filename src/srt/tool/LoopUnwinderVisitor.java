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

        int bound;
        // If the bound is null, use the default
        if (whileStmt.getBound() == null) {
            bound = defaultUnwindBound;
        } else {
        	bound = whileStmt.getBound().getValue();
        }
        
        Expr whileCondition = whileStmt.getCondition();

        Stmt verificationStatement = getVerificationStatement(whileCondition);
        
        // If bound is 0, just replace the whole thing with the possible assert + assume
        if (bound == 0 ){
        	return verificationStatement;
        }
        // Else unroll it once and recurse on the decremented while
    
        // Decremented while loop
        whileStmt = new WhileStmt(whileCondition, new IntLiteral(bound - 1),
        		whileStmt.getInvariantList(), whileStmt.getBody());
        
        // Use body + the decremented while loop to make up the next body
        List<Stmt> unrolledIfBody = new ArrayList<Stmt>();
        unrolledIfBody.addAll(((BlockStmt) whileStmt.getBody()).getStmtList().getStatements());
    	unrolledIfBody.add((Stmt) visit(whileStmt));

        return new IfStmt(whileCondition, 
        		new BlockStmt(new StmtList(unrolledIfBody)), new EmptyStmt());
	}

    // Creates the assert(!c) and assume(!c) statements for the end of the loop body
    // Based on whether or not we're using sound or unsound loop unwinding
    private Stmt getVerificationStatement(Expr condition) {
        
        List<Stmt> assumeAssert = new ArrayList<Stmt>();
        if (unwindingAssertions) {
        	assumeAssert.add(new AssertStmt(negate(condition)));
        }
        assumeAssert.add(new AssumeStmt(negate(condition)));
        
        return new BlockStmt(new StmtList(assumeAssert));
    }

	private Expr negate(Expr expr) {
        return new UnaryExpr(UnaryExpr.LNOT, expr); 
    }
}
