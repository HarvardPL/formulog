package edu.harvard.seas.pl.formulog.symbols;

import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.bool;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.cmp;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInConstructorTesterSymbol implements Symbol {

	IS_CMP_LT("is_cmp_lt", cmp, smt(bool)),
	
	IS_CMP_EQ("is_cmp_eq", cmp, smt(bool)),
	
	IS_CMP_GT("is_cmp_gt", cmp, smt(bool)),
	
	IS_NIL("is_nil", list(a), smt(bool)),
	
	IS_CONS("is_cons", list(a), smt(bool)),
	
	IS_NONE("is_none", option(a), smt(bool)),
	
	IS_SOME("is_some", option(a), smt(bool)),
	
	;

	private final Type type;
	private final String name;

	private BuiltInConstructorTesterSymbol(String name, Type...types) {
		this.name = name;
		List<Type> argTypes = new ArrayList<>(Arrays.asList(types));
		Type retType = argTypes.remove(types.length - 1);
		type = new FunctorType(argTypes, retType);
	}
	
	@Override
	public int getArity() {
		return 1;
	}

	@Override
	public SymbolType getSymbolType() {
		return SymbolType.SOLVER_CONSTRUCTOR_TESTER;
	}

	@Override
	public Type getCompileTimeType() {
		return type;
	}
	
	@Override
	public String toString() {
		return name;
	}
	
	public static void registerAll(SymbolManager symbolManager) {
		for (Symbol sym : BuiltInConstructorTesterSymbol.values()) {
			symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		}
	}

}
