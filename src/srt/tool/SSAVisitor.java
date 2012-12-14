package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
	private Map<String, Integer> index = new HashMap<String, Integer>();
	private boolean beingAssignedTo = false;
	
	public SSAVisitor() {
		super(true);
	}
	
	private String getSSAName(String name) {
		String newName;
		if (index.containsKey(name)){
			newName = String.format("%s$%s", name, index.get(name));
		} else {
			newName = String.format("%s$0", name);
		}
		return newName;
	}
	
	private void incrementSSAIndex(String name) {
		if (index.containsKey(name)){
			index.put(name, (index.get(name) + 1));
		} else {
			index.put(name, 1);
		}
	}
	
	@Override
	public Object visit(Decl decl) {
		return new Decl(getSSAName(decl.getName()), decl.getType(), decl);
	}
	
	@Override
	public Object visit(DeclRef declRef) {
		if (beingAssignedTo) {
			incrementSSAIndex(declRef.getName());
		}
		return new DeclRef(getSSAName(declRef.getName()), declRef);
	}
	
	@Override
	public Object visit(AssignStmt assignment) {
		DeclRef lhs = assignment.getLhs();
		Expr rhs = assignment.getRhs();
		
		Expr newRhs = (Expr) visit(rhs);
		
		beingAssignedTo = true;
		DeclRef newLhs = (DeclRef) visit(lhs);
		beingAssignedTo = false;
		
		return new AssignStmt(newLhs, newRhs, assignment);
	}

}
