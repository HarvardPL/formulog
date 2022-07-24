package edu.harvard.seas.pl.formulog.souffle;

public class SouffleGenException extends Exception {

    SouffleGenException(String message) {
        super(message);
    }

    SouffleGenException(Exception cause) {
        super(cause);
    }

}
