package org.syntax.stella.exceptions;

public abstract class MyException extends Exception {
    protected MyException(String message) {
        super(message);
    }
}
