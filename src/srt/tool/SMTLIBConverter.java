package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;

public class SMTLIBConverter {
	
	private ExprToSmtlibVisitor exprConverter;
	private StringBuilder query;
	
	public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {
		
		if(propertyExprs.size() == 0)
		{
			throw new IllegalArgumentException("No assertions.");
		}
		
		exprConverter = new ExprToSmtlibVisitor();
		query = new StringBuilder("(set-logic QF_BV)\n" +
				"(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n" +
				"(define-fun tobool ((q (_ BitVec 32))) (Bool) (ite (= q (_ bv1 32)) true false))\n");
		// TODO: Define more functions above (for convenience), as needed.
		
		
		// TODO: Declare variables, add constraints, add properties to check
		// here.
		for (String variable : variableNames) {
			query.append(String.format("(declare-fun %s () (_ BitVec 32))\n", variable));
		}
		
		for (Expr expr : transitionExprs) {
			query.append("(assert (tobool " + exprConverter.visit(expr)+ "))\n");
		}
		
		for (Expr expr : propertyExprs) {
			query.append("(assert (tobool " + exprConverter.visit(expr)+ "))\n");
		}
		
		query.append("(check-sat)\n");
		
	}

	public String getQuery() {
		return query.toString();
	}
	
	public List<Integer> getPropertiesThatFailed(String queryResult) {
		List<Integer> res = new ArrayList<Integer>();
		
		return res;
	}
	
}
