package srt.tool.exception;

import srt.ast.visitor.impl.Checker.CheckerError;

public class CheckerException extends Exception {

	/**
	 *
	 */
	private static final long serialVersionUID = 1L;
	private CheckerError checkerError;

	public CheckerException(CheckerError checkerError) {
		this.checkerError = checkerError;
	}

	@Override
	public String getMessage() {
		return checkerError.message;
	}

	public CheckerError getCheckerError() {
		return checkerError;
	}
}
