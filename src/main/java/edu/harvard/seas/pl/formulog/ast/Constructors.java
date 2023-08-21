package edu.harvard.seas.pl.formulog.ast;

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

import edu.harvard.seas.pl.formulog.Configuration;
import edu.harvard.seas.pl.formulog.smt.SmtLibShim;
import edu.harvard.seas.pl.formulog.symbols.BuiltInConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.ConstructorSymbol;
import edu.harvard.seas.pl.formulog.symbols.FunctionSymbol;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager;
import edu.harvard.seas.pl.formulog.symbols.GlobalSymbolManager.TupleSymbol;
import edu.harvard.seas.pl.formulog.symbols.RecordSymbol;
import edu.harvard.seas.pl.formulog.symbols.parameterized.BuiltInConstructorSymbolBase;
import edu.harvard.seas.pl.formulog.symbols.parameterized.Param;
import edu.harvard.seas.pl.formulog.symbols.parameterized.ParameterizedConstructorSymbol;
import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.AlgebraicDataType;
import edu.harvard.seas.pl.formulog.types.Types.Type;
import edu.harvard.seas.pl.formulog.types.Types.TypeIndex;
import edu.harvard.seas.pl.formulog.util.FunctorUtil;
import edu.harvard.seas.pl.formulog.util.FunctorUtil.Memoizer;
import edu.harvard.seas.pl.formulog.util.Util;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import org.pcollections.PMap;

public final class Constructors {

  private Constructors() {
    throw new AssertionError();
  }

  private static final Memoizer<Constructor> memo = new Memoizer<>();

  public static Constructor make(ConstructorSymbol sym, Term[] args) {
    assert sym.getArity() == args.length : sym + " " + Arrays.toString(args);
    if (sym instanceof BuiltInConstructorSymbol) {
      return lookupOrCreateBuiltInConstructor((BuiltInConstructorSymbol) sym, args);
    }
    if (sym instanceof ParameterizedConstructorSymbol) {
      return lookupOrCreateParameterizedConstructor((ParameterizedConstructorSymbol) sym, args);
    }
    if (sym instanceof TupleSymbol) {
      return memo.lookupOrCreate(sym, args, () -> new Tuple((TupleSymbol) sym, args));
    }
    if (sym instanceof RecordSymbol) {
      return memo.lookupOrCreate(sym, args, () -> new Record((RecordSymbol) sym, args));
    }
    switch (sym.getConstructorSymbolType()) {
      case SOLVER_UNINTERPRETED_FUNCTION:
        return memo.lookupOrCreate(sym, args, () -> new SolverUninterpretedFunction(sym, args));
      case SOLVER_CONSTRUCTOR_TESTER:
        return memo.lookupOrCreate(sym, args, () -> makeConstructorTester(sym, args));
      case SOLVER_CONSTRUCTOR_GETTER:
        return memo.lookupOrCreate(sym, args, () -> makeConstructorGetter(sym, args));
      case INDEX_CONSTRUCTOR:
      case VANILLA_CONSTRUCTOR:
        return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
      default:
        throw new IllegalArgumentException(
            "Cannot create constructor for non-constructor symbol " + sym + ".");
    }
  }

  public static Constructor makeZeroAry(ConstructorSymbol sym) {
    return make(sym, Terms.emptyArray());
  }

  private static final Constructor nil = makeZeroAry(BuiltInConstructorSymbol.NIL);

  public static Constructor nil() {
    return nil;
  }

  public static Constructor cons(Term hd, Term tl) {
    return make(BuiltInConstructorSymbol.CONS, new Term[] {hd, tl});
  }

  private static final Constructor none = makeZeroAry(BuiltInConstructorSymbol.NONE);

  public static final Term none() {
    return none;
  }

  public static Term some(Term arg) {
    return make(BuiltInConstructorSymbol.SOME, Terms.singletonArray(arg));
  }

  public static Term tuple(Term... args) {
    return make(GlobalSymbolManager.lookupTupleSymbol(args.length), args);
  }

  private static Constructor lookupOrCreateBuiltInConstructor(
      BuiltInConstructorSymbol sym, Term[] args) {
    Function<String, Constructor> makeSolverOp =
        op -> memo.lookupOrCreate(sym, args, () -> new SolverOperation(sym, args, op));
    switch (sym) {
      case NIL:
        return makeNil(sym, args);
      case CONS:
        return makeCons(sym, args);
      case CMP_EQ:
      case CMP_GT:
      case CMP_LT:
      case NONE:
      case SOME:
        return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
      case SMT_AND:
        return makeAnd(args);
      case SMT_IMP:
        return makeSolverOp.apply("=>");
      case SMT_ITE:
        return memo.lookupOrCreate(sym, args, () -> new SolverIte(sym, args));
      case SMT_NOT:
        return makeSolverOp.apply("not");
      case SMT_OR:
        return makeOr(args);
      case SMT_EXISTS:
      case SMT_FORALL:
        return memo.lookupOrCreate(sym, args, () -> new Quantifier(sym, args));
      case BV_ADD:
        return makeSolverOp.apply("bvadd");
      case BV_AND:
        return makeSolverOp.apply("bvand");
      case BV_MUL:
        return makeSolverOp.apply("bvmul");
      case BV_NEG:
        return makeSolverOp.apply("bvneg");
      case BV_OR:
        return makeSolverOp.apply("bvor");
      case BV_SDIV:
        return makeSolverOp.apply("bvsdiv");
      case BV_UDIV:
        return makeSolverOp.apply("bvudiv");
      case BV_SREM:
        return makeSolverOp.apply("bvsrem");
      case BV_UREM:
        return makeSolverOp.apply("bvurem");
      case BV_SUB:
        return makeSolverOp.apply("bvsub");
      case BV_XOR:
        return makeSolverOp.apply("bvxor");
      case BV_SHL:
        return makeSolverOp.apply("bvshl");
      case BV_ASHR:
        return makeSolverOp.apply("bvashr");
      case BV_LSHR:
        return makeSolverOp.apply("bvlshr");
      case FP_ADD:
        return makeSolverOp.apply("fp.add");
      case FP_DIV:
        return makeSolverOp.apply("fp.div");
      case FP_MUL:
        return makeSolverOp.apply("fp.mul");
      case FP_NEG:
        return makeSolverOp.apply("fp.neg");
      case FP_REM:
        return makeSolverOp.apply("fp.rem");
      case FP_SUB:
        return makeSolverOp.apply("fp.sub");
      case ARRAY_STORE:
        return makeSolverOp.apply("store");
      case ARRAY_CONST:
        return makeSolverOp.apply("const");
      case INT_ABS:
        return makeSolverOp.apply("abs");
      case INT_ADD:
        return makeSolverOp.apply("+");
      case INT_BIG_CONST:
      case INT_CONST:
        return makeIntConst(sym, args);
      case INT_DIV:
        return makeSolverOp.apply("div");
      case INT_GE:
        return makeSolverOp.apply(">=");
      case INT_GT:
        return makeSolverOp.apply(">");
      case INT_LE:
        return makeSolverOp.apply("<=");
      case INT_LT:
        return makeSolverOp.apply("<");
      case INT_MUL:
        return makeSolverOp.apply("*");
      case INT_NEG:
        return makeSolverOp.apply("-");
      case INT_MOD:
        return makeSolverOp.apply("mod");
      case INT_SUB:
        return makeSolverOp.apply("-");
      case STR_AT:
        return makeSolverOp.apply("str.at");
      case STR_CONCAT:
        return makeSolverOp.apply("str.++");
      case STR_CONTAINS:
        return makeSolverOp.apply("str.contains");
      case STR_INDEXOF:
        return makeSolverOp.apply("str.indexof");
      case STR_LEN:
        return makeSolverOp.apply("str.len");
      case STR_PREFIXOF:
        return makeSolverOp.apply("str.prefixof");
      case STR_REPLACE:
        return makeSolverOp.apply("str.replace");
      case STR_SUBSTR:
        return makeSolverOp.apply("str.substr");
      case STR_SUFFIXOF:
        return makeSolverOp.apply("str.suffixof");
      case ENTER_FORMULA:
        return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
      case EXIT_FORMULA:
        return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
    }
    throw new AssertionError("impossible");
  }

  private static Constructor makeAnd(Term[] args) {
    ConstructorSymbol sym = BuiltInConstructorSymbol.SMT_AND;
    return memo.lookupOrCreate(
        sym,
        args,
        () -> {
          return new SolverOperation(sym, args, "and");
        });
  }

  private static Constructor makeOr(Term[] args) {
    ConstructorSymbol sym = BuiltInConstructorSymbol.SMT_OR;
    return memo.lookupOrCreate(
        sym,
        args,
        () -> {
          return new SolverOperation(sym, args, "or");
        });
  }

  // Used for renaming variables to avoid capture.
  private static final Map<PMap<SolverVariable, SmtLibTerm>, SolverVariable> binderMemo =
      new ConcurrentHashMap<>();

  private static final AtomicInteger cnt = new AtomicInteger();

  private static SolverVariable renameBinder(SolverVariable x) {
    ParameterizedConstructorSymbol sym = x.getSymbol();
    sym = sym.copyWithNewArgs(Param.wildCard(), sym.getArgs().get(1));
    return (SolverVariable)
        make(sym, Terms.singletonArray(Terms.makeDummyTerm(cnt.getAndIncrement())));
  }

  private static class SolverLet extends AbstractConstructor<ConstructorSymbol> {

    public static Constructor make(ConstructorSymbol sym, Term[] args) {
      return memo.lookupOrCreate(
          sym,
          args,
          () -> {
            return new SolverLet(sym, args);
          });
    }

    private SolverLet(ConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      shim.print("(let ((");
      ((SmtLibTerm) args[0]).toSmtLib(shim);
      shim.print(" ");
      ((SmtLibTerm) args[1]).toSmtLib(shim);
      shim.print(")) ");
      ((SmtLibTerm) args[2]).toSmtLib(shim);
      shim.print(")");
    }

    @Override
    public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
      // Rename bound variable to avoid variable capture.
      SolverVariable x = (SolverVariable) args[0];
      SolverVariable y = Util.lookupOrCreate(binderMemo, subst, () -> renameBinder(x));
      Term[] newArgs = new Term[args.length];
      newArgs[0] = y;
      newArgs[1] = ((SmtLibTerm) args[1]).substSolverTerms(subst);
      newArgs[2] = ((SmtLibTerm) args[2]).substSolverTerms(subst.plus(x, y));
      return (SmtLibTerm) copyWithNewArgs(newArgs);
    }

    @Override
    public String toString() {
      return "(#let " + args[0] + " = " + args[1] + " in " + args[2] + ")";
    }

    @Override
    public Set<SolverVariable> freeVars() {
      Set<SolverVariable> vars = new HashSet<>(((SmtLibTerm) args[2]).freeVars());
      vars.remove((SolverVariable) args[0]);
      vars.addAll(((SmtLibTerm) args[1]).freeVars());
      return vars;
    }
  }

  private static class Quantifier extends AbstractConstructor<BuiltInConstructorSymbol> {

    protected Quantifier(BuiltInConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    private boolean isExists() {
      return sym.equals(BuiltInConstructorSymbol.SMT_EXISTS);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      String quantifier = "forall (";
      if (isExists()) {
        quantifier = "exists (";
      }
      shim.print("(");
      shim.print(quantifier);
      for (Term t : getBoundVars()) {
        shim.getTypeAnnotation(BuiltInConstructorSymbol.CONS);
        SolverVariable x = (SolverVariable) t;
        shim.print("(");
        x.toSmtLib(shim);
        shim.print(" ");
        FunctorType ft = (FunctorType) x.getSymbol().getCompileTimeType();
        shim.print(ft.getRetType());
        shim.print(")");
      }
      shim.print(") ");
      // Consume final type annotation for variable list
      shim.getTypeAnnotation(BuiltInConstructorSymbol.NIL);
      List<List<Term>> pats = getPatterns();
      // XXX Need to check if pattern is valid!
      if (!pats.isEmpty()) {
        shim.print("(! ");
      }
      ((SmtLibTerm) args[1]).toSmtLib(shim);
      if (!pats.isEmpty()) {
        for (List<Term> pat : pats) {
          shim.print(" :pattern (");
          shim.getTypeAnnotation(BuiltInConstructorSymbol.CONS);
          for (Iterator<Term> it = pat.iterator(); it.hasNext(); ) {
            shim.getTypeAnnotation(BuiltInConstructorSymbol.CONS);
            Constructor wrappedPat = (Constructor) it.next();
            SmtLibTerm t = (SmtLibTerm) wrappedPat.getArgs()[0];
            t.toSmtLib(shim);
            if (it.hasNext()) {
              shim.print(" ");
            }
          }
          shim.print(")");
          // Consume final type annotation for pattern list
          shim.getTypeAnnotation(BuiltInConstructorSymbol.NIL);
        }
        shim.print(")");
      }
      // Consume final type annotation for pattern list list
      shim.getTypeAnnotation(BuiltInConstructorSymbol.NIL);
      shim.print(")");
    }

    @Override
    public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
      // Rename bound variable to avoid variable capture.
      List<SolverVariable> newVars = new ArrayList<>();
      PMap<SolverVariable, SmtLibTerm> newSubst = subst;
      for (Term t : getBoundVars()) {
        SolverVariable x = (SolverVariable) t;
        SolverVariable y = Util.lookupOrCreate(binderMemo, subst, () -> renameBinder(x));
        newVars.add(y);
        newSubst = subst.plus(x, y);
      }
      Term[] newArgs = new Term[args.length];
      for (int i = 0; i < args.length; ++i) {
        newArgs[i] = ((SmtLibTerm) args[i]).substSolverTerms(newSubst);
      }
      return (SmtLibTerm) copyWithNewArgs(newArgs);
    }

    protected List<List<Term>> getPatterns() {
      List<List<Term>> l = new ArrayList<>();
      for (Term pat : Terms.termToTermList(args[2])) {
        l.add(Terms.termToTermList(pat));
      }
      return l;
    }

    private List<SolverVariable> getBoundVars() {
      List<Term> wrappedVars = Terms.termToTermList(args[0]);
      List<SolverVariable> vars = new ArrayList<>();
      for (Term wrappedVar : wrappedVars) {
        SolverVariable var = (SolverVariable) ((Constructor) wrappedVar).getArgs()[0];
        vars.add(var);
      }
      return vars;
    }

    @Override
    public Set<SolverVariable> freeVars() {
      Set<SolverVariable> vars = super.freeVars();
      vars.removeAll(getBoundVars());
      return vars;
    }
  }

  private static class Nil extends AbstractConstructor<ConstructorSymbol> {

    protected Nil(ConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, shim);
    }

    @Override
    public String toString() {
      return "[]";
    }
  }

  private static class Cons extends AbstractConstructor<ConstructorSymbol> {

    protected Cons(ConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, shim);
    }

    @Override
    public String toString() {
      List<Term> listArgs = new ArrayList<>();
      Term cur = this;
      while (cur instanceof Cons) {
        Cons cons = (Cons) cur;
        listArgs.add(cons.args[0]);
        cur = cons.args[1];
      }
      if (cur instanceof Nil) {
        String s = "[";
        for (Iterator<Term> it = listArgs.iterator(); it.hasNext(); ) {
          s += it.next();
          if (it.hasNext()) {
            s += ", ";
          }
        }
        return s + "]";
      } else {
        String s = "(";
        for (Term t : listArgs) {
          s += t;
          s += " :: ";
        }
        return s + cur + ")";
      }
    }
  }

  private static Constructor makeNil(ConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(sym, args, () -> new Nil(sym, args));
  }

  private static Constructor makeCons(ConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(sym, args, () -> new Cons(sym, args));
  }

  private static Constructor makeIntConst(ConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                String repr = ((Primitive<?>) args[0]).getVal().toString();
                if (repr.charAt(0) == '-') {
                  shim.print("(- " + repr.substring(1, repr.length()) + ")");
                } else {
                  shim.print(repr);
                }
              }
            });
  }

  private static Constructor lookupOrCreateParameterizedConstructor(
      ParameterizedConstructorSymbol sym, Term[] args) {
    Function<String, Constructor> makeSolverOp =
        op -> memo.lookupOrCreate(sym, args, () -> new SolverOperation(sym, args, op));
    BuiltInConstructorSymbolBase preSym = sym.getBase();
    switch (preSym) {
      case SMT_EQ:
        return makeSolverOp.apply("=");
      case SMT_LET:
        return SolverLet.make(sym, args);
      case ARRAY_DEFAULT:
        return makeSolverOp.apply("default");
      case ARRAY_SELECT:
        return makeSolverOp.apply("select");
      case BV_SGE:
        return makeSolverOp.apply("bvsge");
      case BV_SGT:
        return makeSolverOp.apply("bvsgt");
      case BV_SLE:
        return makeSolverOp.apply("bvsle");
      case BV_SLT:
        return makeSolverOp.apply("bvslt");
      case BV_UGE:
        return makeSolverOp.apply("bvuge");
      case BV_UGT:
        return makeSolverOp.apply("bvugt");
      case BV_ULE:
        return makeSolverOp.apply("bvule");
      case BV_ULT:
        return makeSolverOp.apply("bvult");
      case FP_EQ:
        return makeSolverOp.apply("fp.eq");
      case FP_GE:
        return makeSolverOp.apply("fp.geq");
      case FP_GT:
        return makeSolverOp.apply("fp.gt");
      case FP_IS_NAN:
        return makeSolverOp.apply("fp.isNaN");
      case FP_LE:
        return makeSolverOp.apply("fp.leq");
      case FP_LT:
        return makeSolverOp.apply("fp.lt");
      case BV_TO_BV_SIGNED:
        return makeBvToBvSigned(sym, args);
      case BV_TO_BV_UNSIGNED:
        return makeBvToBvUnsigned(sym, args);
      case FP_TO_FP:
        return makeFpToFp(sym, args);
      case BV_TO_FP:
        return makeBvToFp(sym, args);
      case FP_TO_SBV:
        return makeFpToBv(sym, args, true);
      case FP_TO_UBV:
        return makeFpToBv(sym, args, false);
      case BV_CONST:
        return makeBvConst(sym, args);
      case BV_BIG_CONST:
        return makeBvBigConst(sym, args);
      case INT_TO_BV:
        return makeIntToBv(sym, args);
      case BV_TO_INT:
        return makeSolverOp.apply("bv2int");
      case BV_CONCAT:
        return makeSolverOp.apply("concat");
      case BV_EXTRACT:
        return makeBvExtract(sym, args);
      case FP_BIG_CONST:
      case FP_CONST:
        return makeConstant(sym, args);
      case SMT_PAT:
      case SMT_WRAP_VAR:
        return memo.lookupOrCreate(sym, args, () -> new VanillaConstructor(sym, args));
      case SMT_VAR:
        return memo.lookupOrCreate(sym, args, () -> new SolverVariable(sym, args));
    }
    throw new AssertionError("impossible");
  }

  private static int nat(Param param) {
    return ((TypeIndex) param.getType()).getIndex();
  }

  private static int nat(ParameterizedConstructorSymbol sym, int idx) {
    return nat(sym.getArgs().get(idx));
  }

  private static Constructor makeBvConst(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                I32 arg = (I32) args[0];
                int width = nat(sym.getArgs().get(0));
                String s = Integer.toBinaryString(arg.getVal());
                shim.print(formatBitString(s, width));
              }
            });
  }

  private static Constructor makeBvBigConst(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                I64 arg = (I64) args[0];
                int width = nat(sym.getArgs().get(0));
                String s = Long.toBinaryString(arg.getVal());
                shim.print(formatBitString(s, width));
              }
            });
  }

  private static String formatBitString(String bitString, int width) {
    int len = bitString.length();
    if (width > len) {
      String pad = "";
      for (int w = len; w < width; w++) {
        pad += "0";
      }
      bitString = pad + bitString;
    } else if (width < len) {
      bitString = bitString.substring(len - width, len);
    }
    return "#b" + bitString;
  }

  private static Constructor makeIntToBv(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {
              @Override
              public void toSmtLib(SmtLibShim shim) {
                shim.print("((_ int2bv ");
                int width = nat(sym.getArgs().get(0));
                shim.print(width + ") ");
                ((SmtLibTerm) args[0]).toSmtLib(shim);
                shim.print(")");
              }
            });
  }

  private static Constructor makeBvExtract(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {
              @Override
              public void toSmtLib(SmtLibShim shim) {
                shim.print("((_ extract ");
                shim.print(args[2] + " " + args[1] + ") ");
                ((SmtLibTerm) args[0]).toSmtLib(shim);
                shim.print(")");
              }
            });
  }

  private static Constructor makeConstant(ConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                ((SmtLibTerm) args[0]).toSmtLib(shim);
              }
            });
  }

  private static Constructor makeBvToBvSigned(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                int idx1 = nat(sym, 0);
                int idx2 = nat(sym, 1);
                SmtLibTerm t = (SmtLibTerm) args[0];
                if (idx1 < idx2) {
                  shim.print("(");
                  shim.print("(_ sign_extend " + (idx2 - idx1) + ") ");
                  t.toSmtLib(shim);
                  shim.print(")");
                } else if (idx1 == idx2) {
                  t.toSmtLib(shim);
                } else {
                  shim.print("(");
                  shim.print("(_ extract " + (idx2 - 1) + " 0) ");
                  t.toSmtLib(shim);
                  shim.print(")");
                }
              }
            });
  }

  private static Constructor makeBvToBvUnsigned(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                int idx1 = nat(sym, 0);
                int idx2 = nat(sym, 1);
                SmtLibTerm t = (SmtLibTerm) args[0];
                if (idx1 < idx2) {
                  shim.print("(");
                  shim.print("(_ zero_extend " + (idx2 - idx1) + ") ");
                  t.toSmtLib(shim);
                  shim.print(")");
                } else if (idx1 == idx2) {
                  t.toSmtLib(shim);
                } else {
                  shim.print("(");
                  shim.print("(_ extract " + (idx2 - 1) + " 0) ");
                  t.toSmtLib(shim);
                  shim.print(")");
                }
              }
            });
  }

  private static Constructor makeBvToFp(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                int exponent = nat(sym, 1);
                int significand = nat(sym, 2);
                shim.print("((_ to_fp " + exponent + " " + significand + ") RNE ");
                ((SmtLibTerm) args[0]).toSmtLib(shim);
                shim.print(")");
              }
            });
  }

  private static Constructor makeFpToFp(ParameterizedConstructorSymbol sym, Term[] args) {
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                int exponent = nat(sym, 2);
                int significand = nat(sym, 3);
                shim.print("((_ to_fp " + exponent + " " + significand + ") RNE ");
                ((SmtLibTerm) args[0]).toSmtLib(shim);
                shim.print(")");
              }
            });
  }

  private static Constructor makeFpToBv(
      ParameterizedConstructorSymbol sym, Term[] args, boolean signed) {
    String s = signed ? "fp.to_sbv" : "fp.to_ubv";
    return memo.lookupOrCreate(
        sym,
        args,
        () ->
            new AbstractConstructor<ParameterizedConstructorSymbol>(sym, args) {

              @Override
              public void toSmtLib(SmtLibShim shim) {
                int width = nat(sym, 2);
                shim.print("((_ " + s + " " + width + ") RNE ");
                ((SmtLibTerm) args[0]).toSmtLib(shim);
                shim.print(")");
              }
            });
  }

  private abstract static class AbstractConstructor<S extends ConstructorSymbol>
      extends AbstractTerm implements Constructor {

    protected final S sym;
    protected final Term[] args;
    protected final boolean isGround;
    protected final boolean containsFunctionCall;

    protected AbstractConstructor(S sym, Term[] args) {
      assert noneNull(args) : sym;
      this.sym = sym;
      this.args = args;
      boolean g = true;
      boolean f = false;
      for (Term t : args) {
        g &= t.isGround();
        f |= t.containsUnevaluatedTerm();
      }
      isGround = g;
      containsFunctionCall = f;
    }

    private boolean noneNull(Term[] ts) {
      for (Term t : ts) {
        if (t == null) {
          return false;
        }
      }
      return true;
    }

    @Override
    public boolean isGround() {
      return isGround;
    }

    @Override
    public boolean containsUnevaluatedTerm() {
      return containsFunctionCall;
    }

    @Override
    public S getSymbol() {
      return sym;
    }

    @Override
    public Term[] getArgs() {
      return args;
    }

    @Override
    public String toString() {
      return FunctorUtil.toString(sym, args);
    }

    @Override
    public Term copyWithNewArgs(Term[] args) {
      return make(sym, args);
    }

    @Override
    public SmtLibTerm substSolverTerms(PMap<SolverVariable, SmtLibTerm> subst) {
      if (subst.containsKey(this)) {
        return subst.get(this);
      }
      Term[] newArgs = new Term[args.length];
      for (int i = 0; i < args.length; ++i) {
        newArgs[i] = ((SmtLibTerm) args[i]).substSolverTerms(subst);
      }
      return (SmtLibTerm) copyWithNewArgs(newArgs);
    }

    @Override
    public Set<SolverVariable> freeVars() {
      Set<SolverVariable> vars = new HashSet<>();
      for (Term t : args) {
        vars.addAll(((SmtLibTerm) t).freeVars());
      }
      return vars;
    }
  }

  public static class VanillaConstructor extends AbstractConstructor<ConstructorSymbol> {

    private VanillaConstructor(ConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, shim);
    }
  }

  public static class Tuple extends AbstractConstructor<TupleSymbol> {

    private Tuple(TupleSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, shim);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder("(");
      for (int i = 0; i < args.length; ++i) {
        sb.append(args[i]);
        if (i < args.length - 1) {
          sb.append(", ");
        }
      }
      sb.append(")");
      return sb.toString();
    }
  }

  public static class Record extends AbstractConstructor<ConstructorSymbol> {

    private Record(RecordSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, shim);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder("{ ");
      int i = 0;
      for (FunctionSymbol label : ((RecordSymbol) sym).getLabels()) {
        sb.append(label);
        sb.append("=");
        sb.append(args[i]);
        sb.append("; ");
        ++i;
      }
      sb.append("}");
      return sb.toString();
    }
  }

  public static class SolverVariable extends AbstractConstructor<ParameterizedConstructorSymbol> {

    private static final AtomicInteger cnt = new AtomicInteger();
    /**
     * The unique numeric identifier for this solver variable, <i>as a solver variable</i>. This is
     * distinct from the numeric identifier of this solver variable <i>as a general term</i>. Having
     * a second ID for a solver variable is helpful because it (typically) is much smaller than the
     * term ID, making it easier to read in SMT formulas.
     */
    private final int solverVarId = cnt.getAndIncrement();

    public SolverVariable(ParameterizedConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      shim.print(this);
    }

    public int getSolverVarId() {
      return solverVarId;
    }

    @Override
    public String toString() {
      if (Configuration.simplifyFormulaVars) {
        return "#x" + getSolverVarId();
      }
      Type ty = ((FunctorType) sym.getCompileTimeType()).getRetType();
      ty = ((AlgebraicDataType) ty).getTypeArgs().get(0);
      return "#{" + args[0] + "}[" + ty + "]";
    }

    @Override
    public Set<SolverVariable> freeVars() {
      return Collections.singleton(this);
    }
  }

  private static Constructor makeConstructorTester(ConstructorSymbol sym, Term[] args) {
    assert sym.toString().matches("#is_.*");
    String s = "|is-" + sym.toString().substring(4) + "|";
    return new AbstractConstructor<ConstructorSymbol>(sym, args) {

      @Override
      public void toSmtLib(SmtLibShim shim) {
        shim.print("(");
        shim.print(s);
        shim.print(" ");
        ((SmtLibTerm) args[0]).toSmtLib(shim);
        shim.print(")");
      }
    };
  }

  private static Constructor makeConstructorGetter(ConstructorSymbol sym, Term[] args) {
    String s = "|" + sym.toString() + "|";
    return new AbstractConstructor<ConstructorSymbol>(sym, args) {

      @Override
      public void toSmtLib(SmtLibShim shim) {
        shim.print("(");
        shim.print(s);
        shim.print(" ");
        ((SmtLibTerm) args[0]).toSmtLib(shim);
        shim.print(")");
      }
    };
  }

  public static class SolverUninterpretedFunction extends AbstractConstructor<ConstructorSymbol> {

    protected SolverUninterpretedFunction(ConstructorSymbol sym, Term[] args) {
      super(sym, args);
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, shim);
    }
  }

  public static class SolverOperation extends AbstractConstructor<ConstructorSymbol> {

    private final String op;

    protected SolverOperation(ConstructorSymbol sym, Term[] args, String op) {
      super(sym, args);
      this.op = op;
    }

    @Override
    public void toSmtLib(SmtLibShim shim) {
      Constructors.toSmtLib(this, op, shim);
    }

    private String getSyntax() {
      if (sym instanceof ParameterizedConstructorSymbol) {
        if (((ParameterizedConstructorSymbol) sym)
            .getBase()
            .equals(BuiltInConstructorSymbolBase.SMT_EQ)) {
          return "#=";
        }
      }
      if (sym instanceof BuiltInConstructorSymbol) {
        switch ((BuiltInConstructorSymbol) sym) {
          case SMT_AND:
            return "/\\";
          case SMT_IMP:
            return "==>";
          case SMT_NOT:
            return "~";
          case SMT_OR:
            return "\\/";
          default:
            return null;
        }
      }
      return null;
    }

    @Override
    public String toString() {
      String syntax = getSyntax();
      if (syntax == null) {
        return super.toString();
      }
      if (args.length == 1) {
        return "(" + syntax + " " + args[0] + ")";
      }
      if (args.length == 2) {
        return "(" + args[0] + " " + syntax + " " + args[1] + ")";
      }
      throw new AssertionError("impossible");
    }
  }

  private static class SolverIte extends SolverOperation {

    protected SolverIte(ConstructorSymbol sym, Term[] args) {
      super(sym, args, "ite");
    }

    @Override
    public String toString() {
      return "(#if " + args[0] + " then " + args[1] + " else " + args[2] + ")";
    }
  }

  private static void toSmtLib(Constructor c, String repr, SmtLibShim shim) {
    ConstructorSymbol sym = c.getSymbol();
    if (sym.getArity() > 0) {
      shim.print("(");
    }
    String typeAnnotation = shim.getTypeAnnotation(sym);
    if (typeAnnotation != null) {
      shim.print("(as ");
      shim.print(repr);
      shim.print(" ");
      shim.print(typeAnnotation);
      shim.print(")");
    } else {
      shim.print(repr);
    }
    for (Term t : c.getArgs()) {
      SmtLibTerm tt = (SmtLibTerm) t;
      shim.print(" ");
      tt.toSmtLib(shim);
    }
    if (sym.getArity() > 0) {
      shim.print(")");
    }
  }

  private static void toSmtLib(Constructor c, SmtLibShim shim) {
    toSmtLib(c, c.getSymbol().toString(), shim);
  }
}
