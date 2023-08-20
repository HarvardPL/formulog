package edu.harvard.seas.pl.formulog.parsing;

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

public class ParsingTest {

  void test(String file) {
    boolean isBad = file.matches("test\\d\\d\\d_bd.flg");
    try {
      InputStream is = getClass().getClassLoader().getResourceAsStream(file);
      if (is == null) {
        throw new FileNotFoundException(file + " not found");
      }
      (new Parser()).parse(new InputStreamReader(is));
    } catch (ParseException e) {
      if (!isBad) {
        fail("Test failed for a good program: " + e.getMessage());
      }
      return;
    } catch (Exception e) {
      fail("Unexpected exception: " + e.getMessage() + " " + e.getClass());
    }
    if (isBad) {
      fail("Test succeeded for a bad program");
    }
  }

  @Test
  public void test001() {
    test("test001_ok.flg");
  }

  @Test
  public void test002() {
    test("test002_ok.flg");
  }

  @Test
  public void test003() {
    test("test003_ok.flg");
  }

  @Test
  public void test004() {
    test("test004_ok.flg");
  }

  @Test
  public void test005() {
    test("test005_ok.flg");
  }

  @Test
  public void test006() {
    test("test006_ok.flg");
  }

  @Test
  public void test007() {
    test("test007_ok.flg");
  }

  @Test
  public void test028() {
    test("test028_ok.flg");
  }

  @Test
  public void test031() {
    test("test031_ok.flg");
  }

  @Test
  public void test036() {
    test("test036_ok.flg");
  }

  @Test
  public void test042() {
    test("test042_ok.flg");
  }

  @Test
  public void test055() {
    test("test055_bd.flg");
  }

  @Test
  public void test059() {
    test("test059_ok.flg");
  }

  @Test
  public void test074() {
    test("test074_ok.flg");
  }

  @Test
  public void test075() {
    test("test075_ok.flg");
  }

  @Test
  public void test076() {
    test("test076_ok.flg");
  }

  @Test
  public void test255() {
    test("test255_bd.flg");
  }

  @Test
  public void test257() {
    test("test257_ok.flg");
  }

  @Test
  public void test266() {
    test("test266_bd.flg");
  }

  @Test
  public void test271() {
    test("test271_bd.flg");
  }

  @Test
  public void test272() {
    test("test272_bd.flg");
  }

  @Test
  public void test302() {
    test("test302_bd.flg");
  }

  @Test
  public void test322() {
    test("test322_bd.flg");
  }

  @Test
  public void test335() {
    test("test335_bd.flg");
  }
}
