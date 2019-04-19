package edu.harvard.seas.pl.formulog.ast;

import edu.harvard.seas.pl.formulog.ast.Atoms.Atom;

public interface Rule {

	/*
	 * TODO Instead of returning the whole list, should probably just provide
	 * methods to index into head/body and get size of each.
	 * 
	 * Could maybe provide all of head/body as Iterable.
	 */

	public Iterable<Atom> getHead();

	public Iterable<Atom> getBody();
	
	public int getHeadSize();
	
	public int getBodySize();
	
	public Atom getHead(int idx);
	
	public Atom getBody(int idx);

}
