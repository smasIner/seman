package org.stella;

import org.junit.jupiter.api.*;
import org.junit.jupiter.params.*;
import org.junit.jupiter.params.provider.*;
import org.stella.typecheck.TypeError;

import static org.junit.jupiter.api.Assertions.*;
import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.stream.*;

class MainTest {

    static List<String> getAllFilesInSubdirectories(String rootDirectory, String subDirectory) throws IOException {
        Path rootPath = Paths.get(rootDirectory);
        if (!Files.exists(rootPath)) {
            return Collections.emptyList();
        }

        try (Stream<Path> paths = Files.walk(rootPath)) {
            return paths.filter(Files::isRegularFile)
                    .filter(path -> path.toString().contains(File.separator + subDirectory + File.separator))
                    .map(Path::toString)
                    .collect(Collectors.toList());
        }
    }

    @ParameterizedTest(name = "{index} Typechecking well-typed program {0}")
    @MethodSource("wellTypedFiles")
    void testWellTyped(String filepath) throws Exception {
        String[] args = new String[0];
        final InputStream original = System.in;
        final FileInputStream fips = new FileInputStream(filepath);
        System.setIn(fips);
        Assertions.assertDoesNotThrow(() -> Main.main(args));
        System.setIn(original);
    }

    static Stream<String> wellTypedFiles() throws IOException {
        return getAllFilesInSubdirectories("tests", "well-typed").stream();
    }

    @ParameterizedTest(name = "{index} Typechecking ill-typed program {0}")
    @MethodSource("illTypedFiles")
    void testIllTyped(String filepath) throws Exception {
        String[] args = new String[0];
        final FileInputStream fips = new FileInputStream(filepath);
        System.setIn(fips);

        // Expecting a TypeError for ill-typed files
        Exception exception = assertThrows(TypeError.class, () -> Main.main(args), "Expected the type checker to fail!");
        System.out.println("Type Error: " + exception.getMessage());
    }

    static Stream<String> illTypedFiles() throws IOException {
        return getAllFilesInSubdirectories("tests", "ill-typed").stream();
    }
}

