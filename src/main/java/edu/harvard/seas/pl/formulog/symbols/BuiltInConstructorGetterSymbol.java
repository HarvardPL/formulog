package edu.harvard.seas.pl.formulog.symbols;

import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.a;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.list;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.option;
import static edu.harvard.seas.pl.formulog.types.BuiltInTypes.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.harvard.seas.pl.formulog.types.FunctorType;
import edu.harvard.seas.pl.formulog.types.Types.Type;

public enum BuiltInConstructorGetterSymbol implements Symbol {

	CONS_1("cons_1", list(a), smt(a)),
	
	CONS_2("cons_2", list(a), smt(list(a))),
	
	SOME_1("some_1", option(a), smt(a))
	
	;

	private final String name;
	private final FunctorType type;
	
	private BuiltInConstructorGetterSymbol(String name, Type...types) {
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
		return SymbolType.SOLVER_CONSTRUCTOR_GETTER;
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
		for (Symbol sym : BuiltInConstructorGetterSymbol.values()) {
			symbolManager.registerSymbol(sym, sym.getCompileTimeType());
		}
	}
	
}
