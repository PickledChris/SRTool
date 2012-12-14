package srt.tool;


import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import srt.ast.Expr;

public class SMTLIBConverter {

	private ExprToSmtlibVisitor exprConverter;
	private StringBuilder query;
	private int assertionCounter = 0;

	public SMTLIBConverter(Set<String> variableNames, List<Expr> transitionExprs, List<Expr> propertyExprs) {

		if(0 == propertyExprs.size())
		{
			throw new IllegalArgumentException("No assertions.");
		}

		exprConverter = new ExprToSmtlibVisitor();
		query = new StringBuilder("(set-logic QF_BV)\n" +
				"(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n" +
				"(define-fun tobool ((x (_ BitVec 32))) (Bool) (not (= x (_ bv0 32))))\n");

		// Declare each variable as a bit vector
		StringBuilder variables = new StringBuilder();
		for (String variable : variableNames) {
			variables.append(String.format("(declare-fun %s () (_ BitVec 32))\n", variable));
		}

		// Declare program constraints
		StringBuilder expressions = new StringBuilder();
		for (Expr expr : transitionExprs) {
			expressions.append(assertion(toBool(exprConverter.visit(expr))));
		}

		
		for (Expr expr : propertyExprs) {
			exprConverter.visit(expr);
			// Dead code from early attempt at assertion reporting
			//String[] proposition = proposition(assertionExpression);
			//variables.append(proposition[0]);
			//expressions.append(assertion(proposition[1]));
		}

		query.append(variables);
		query.append(expressions);

		// Verification condition
		query.append(atLeastOneQueryCanFail(propertyExprs));

		query.append("(check-sat)\n");
		//query.append(String.format("(get-value (%s))", allPropositions()));
		
        //System.out.println(query); //Uncomment for debugging.
	}

	public String getQuery() {
		return query.toString();
	}

	public List<Integer> getPropertiesThatFailed(String queryResult) {
		return new ArrayList<Integer>();
	}

	private String atLeastOneQueryCanFail(Collection<Expr> propertyExprs) {
		String negatedOr = "";
		for (Expr expr : propertyExprs) {
			negatedOr = or(negatedOr, negatedExpr(expr));
		}
		return assertion(negatedOr);
	}

	private String assertion(String condition) {
		return String.format("(assert %s)\n", condition);
	}

	private String toBool(String condition) {
		return String.format("(tobool %s)", condition);
	}

	private String negatedExpr(Expr expr) {
		return String.format("(not (tobool %s))", exprConverter.visit(expr));
	}

	private String or(String lhs, String rhs) {
		return String.format("(or %s %s)", lhs, rhs);
	}

	/*
	 * Dead code from early attempt at assertion 
	private String[] proposition(String assertion) {
		String variableDeclaration = String.format("(declare-fun prop%s () Bool)\n", assertionCounter);
		String proposition = String.format("(= prop%s %s)", assertionCounter, assertion);
		assertionCounter++;
		return new String[]{variableDeclaration, proposition};
	}

	private String allPropositions() {
		String propositions = "";
		for (int x = 0; x < assertionCounter; x++){
			propositions += String.format("prop%s ", x);
		}
		return propositions;
	}
	*/
}
