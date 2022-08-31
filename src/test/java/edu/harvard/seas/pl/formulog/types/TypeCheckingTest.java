package edu.harvard.seas.pl.formulog.types;

/*-
 * #%L
 * Formulog
 * %%
 * Copyright (C) 2018 - 2020 President and Fellows of Harvard College
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */


import static org.junit.Assert.fail;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;

import org.junit.Test;

import edu.harvard.seas.pl.formulog.ast.BasicProgram;
import edu.harvard.seas.pl.formulog.parsing.Parser;

public class TypeCheckingTest {

    void test(String file) {
        boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
        try {
            InputStream is = getClass().getClassLoader().getResourceAsStream(file);
            if (is == null) {
                throw new FileNotFoundException(file + " not found");
            }
            BasicProgram prog = (new Parser()).parse(new InputStreamReader(is));
            (new TypeChecker(prog)).typeCheck();
        } catch (TypeException e) {
            if (!isBad) {
                fail("Test failed for a good program: " + e.getMessage());
            }
            return;
        } catch (Exception e) {
            fail("Unexpected exception: " + e.getMessage());
        }
        if (isBad) {
            fail("Test succeeded for a bad program");
        }
    }

    @Test
    public void test006() {
        test("test006_ok.flg");
    }

    @Test
    public void test008() {
        test("test008_ok.flg");
    }

    @Test
    public void test009() {
        test("test009_ok.flg");
    }

    @Test
    public void test010() {
        test("test010_ok.flg");
    }

    @Test
    public void test011() {
        test("test011_ok.flg");
    }

    @Test
    public void test012() {
        test("test012_bd.flg");
    }

    @Test
    public void test013() {
        test("test013_ok.flg");
    }

    @Test
    public void test014() {
        test("test014_ok.flg");
    }

    @Test
    public void test015() {
        test("test015_ok.flg");
    }

    @Test
    public void test016() {
        test("test016_ok.flg");
    }

    @Test
    public void test017() {
        test("test017_ok.flg");
    }

    @Test
    public void test049() {
        test("test049_ok.flg");
    }

    @Test
    public void test052() {
        test("test052_bd.flg");
    }

    @Test
    public void test053() {
        test("test053_ok.flg");
    }

    @Test
    public void test054() {
        test("test054_ok.flg");
    }

    @Test
    public void test060() {
        test("test060_ok.flg");
    }

    @Test
    public void test080() {
        test("test080_bd.flg");
    }

    @Test
    public void test091() {
        test("test091_bd.flg");
    }

    @Test
    public void test098() {
        test("test098_bd.flg");
    }

    @Test
    public void test118() {
        test("test118_bd.flg");
    }

    @Test
    public void test130() {
        test("test130_bd.flg");
    }

    @Test
    public void test131() {
        test("test131_bd.flg");
    }

    @Test
    public void test132() {
        test("test132_bd.flg");
    }

    @Test
    public void test185() {
        test("test185_bd.flg");
    }

    @Test
    public void test188() {
        test("test188_bd.flg");
    }

    @Test
    public void test268() {
        test("test268_bd.flg");
    }

    @Test
    public void test269() {
        test("test269_bd.flg");
    }

    @Test
    public void test270() {
        test("test270_bd.flg");
    }

    @Test
    public void test293() {
        test("test293_ok.flg");
    }

    @Test
    public void test294() {
        test("test294_ok.flg");
    }

    @Test
    public void test295() {
        test("test295_bd.flg");
    }

    @Test
    public void test296() {
        test("test296_bd.flg");
    }

    @Test
    public void test307() {
        test("test307_ok.flg");
    }

    @Test
    public void test312() {
        test("test312_bd.flg");
    }

    @Test
    public void test313() {
        test("test313_bd.flg");
    }

    @Test
    public void test314() {
        test("test314_bd.flg");
    }

    @Test
    public void test315() {
        test("test315_bd.flg");
    }

    @Test
    public void test327() {
        test("test327_bd.flg");
    }

    @Test
    public void test333() {
        test("test333_bd.flg");
    }

}
