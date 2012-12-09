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

		if(propertyExprs.size() == 0)
		{
			throw new IllegalArgumentException("No assertions.");
		}

		exprConverter = new ExprToSmtlibVisitor();
		query = new StringBuilder("(set-logic QF_BV)\n" +
				"(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n" +
                    "(define-fun tobool ((x (_ BitVec 32))) (Bool) (= x (_ bv1 32)))\n");
		// TODO: Define more functions above (for convenience), as needed.


		// TODO: Declare variables, add constraints, add properties to check
		// here.
		// Declare each variable as a bit vector

		StringBuilder variables = new StringBuilder();
		for (String variable : variableNames) {
			variables.append(String.format("(declare-fun %s () (_ BitVec 32))\n", variable));
		}

		StringBuilder expressions = new StringBuilder();
		for (Expr expr : transitionExprs) {
			expressions.append(assertion(exprConverter.visit(expr)));
		}
		for (Expr expr : propertyExprs) {
			String valueToAssert = exprConverter.visit(expr);
			String[] proposition = proposition(valueToAssert);
			variables.append(proposition[0]);
			expressions.append(assertion(valueToAssert));
			//expressions.append(assertion(proposition[1]));
		}

		query.append(variables);
		query.append(expressions);

		// At least one can fail
		query.append(atLeastOneQueryCanFail(transitionExprs, propertyExprs));

		query.append("(check-sat)\n");
		query.append(String.format("(get-value (%s))", allPropositions()));

        System.out.println(query);
	}

	public String getQuery() {
		return query.toString();
	}

	public List<Integer> getPropertiesThatFailed(String queryResult) {
		List<Integer> res = new ArrayList<Integer>();

		return res;
	}

	private String atLeastOneQueryCanFail(Collection<Expr> transitionExprs, Collection<Expr> propertyExprs) {
		String negatedOr = "";
		for (Expr expr : transitionExprs) {
			negatedOr = or(negatedOr, negatedExpr(expr));
		}
		for (Expr expr : propertyExprs) {
			negatedOr = or(negatedOr, negatedExpr(expr));
		}
		return assertion(negatedOr);
	}

	private String assertion(String condition) {
		return String.format("(assert (tobool %s))\n", condition);
	}

	private String negatedExpr(Expr expr) {
		return String.format("(bvnot %s)", exprConverter.visit(expr));
	}

	private String or(String lhs, String rhs) {
		return String.format("(bvor %s %s)", lhs, rhs);
	}

	private String[] proposition(String assertion) {
		String variableDeclaration = String.format("(declare-fun prop%s () Bool)\n", assertionCounter);
		String proposition = String.format("(= prop%s %s)", assertionCounter, assertion);
		assertionCounter++;
		String[] returnVars =  {variableDeclaration, proposition};
		return returnVars;
	}

	private String allPropositions() {
		String propositions = "";
		for (int x = 0; x < assertionCounter; x++){
			propositions += String.format("prop%s ", x);
		}
		return propositions;
	}

}
