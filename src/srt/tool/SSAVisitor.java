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
	
	// Gets the current SSA value
	private String getSSAName(String name) {
		String newName;
		if (index.containsKey(name)){
			newName = String.format("%s$%s", name, index.get(name));
		} else {
			newName = String.format("%s$0", name);
		}
		return newName;
	}
	
	// Increments the stored count for that value
	private void incrementSSAIndex(String name) {
		if (index.containsKey(name)){
			index.put(name, (index.get(name) + 1));
		} else {
			index.put(name, 1);
		}
	}
	
	// Just replace with the initial reference
	@Override
	public Object visit(Decl decl) {
		return new Decl(getSSAName(decl.getName()), decl.getType(), decl);
	}
	
	// Replace with existing ref unless within an assignment lhs
	// In which case increment and then replace
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
		
		// Increment and modify lhs
		beingAssignedTo = true;
		DeclRef newLhs = (DeclRef) visit(lhs);
		beingAssignedTo = false;
		
		return new AssignStmt(newLhs, newRhs, assignment);
	}

}
