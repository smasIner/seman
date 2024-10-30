package org.stella;

import org.junit.jupiter.api.*;
import org.junit.jupiter.params.*;
import org.junit.jupiter.params.provider.*;

import static org.junit.jupiter.api.Assertions.*;
import java.io.*;

class MainTest {


    @ParameterizedTest(name = "{index} Typechecking well-typed program {0}")
    @ValueSource(strings = {
            "tests/well-typed/factorial.stella",
            "tests/well-typed/squares.stella",
            "tests/well-typed/higher-order-1.stella",
            "tests/well-typed/increment_twice.stella",
            "tests/well-typed/logical-operators.stella"})
    void testWellTyped(String filepath) throws Exception {
        String[] args = new String[0];
        final InputStream original = System.in;
        final FileInputStream fips = new FileInputStream(filepath);
        System.setIn(fips);
        Assertions.assertDoesNotThrow(() -> Main.main(args));
        System.setIn(original);
    }

    @ParameterizedTest(name = "{index} Typechecking ill-typed program {0}")
    @ValueSource(strings = {
            "tests/ill-typed/applying-non-function-1.stella",
            "tests/ill-typed/applying-non-function-2.stella",
            "tests/ill-typed/applying-non-function-3.stella",
            "tests/ill-typed/argument-type-mismatch-1.stella",
            "tests/ill-typed/argument-type-mismatch-2.stella",
            "tests/ill-typed/argument-type-mismatch-3.stella",
            "tests/ill-typed/bad-if-1.stella",
            "tests/ill-typed/bad-if-2.stella",
            "tests/ill-typed/bad-succ-1.stella",
            "tests/ill-typed/bad-succ-2.stella",
            "tests/ill-typed/bad-succ-3.stella",
            "tests/ill-typed/shadowed-variable-1.stella",
            "tests/ill-typed/undefined-variable-1.stella",
            "tests/ill-typed/undefined-variable-2.stella",
            "tests/ill-typed/bad-squares-1.stella",
            "tests/ill-typed/bad-squares-2.stella"})
    void testIllTyped(String filepath) throws Exception {
        String[] args = new String[0];
        final FileInputStream fips = new FileInputStream(filepath);
        System.setIn(fips);

        // Change Exception class to your specific
        Exception exception = assertThrows(Exception.class, () -> Main.main(args), "Expected the type checker to fail!");
        System.out.println("Type Error: " + exception.getMessage());
    }
}
