package org.oxford.comlab.perfectref.parser;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.FileReader;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.oxford.comlab.perfectref.rewriter.PI;
import org.oxford.comlab.perfectref.rewriter.Clause;
//import org.semanticweb.HermiT.Reasoner.Configuration;
import org.semanticweb.HermiT.structural.OWLAxioms;
import org.semanticweb.HermiT.structural.OWLNormalization;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasoner;
//import org.semanticweb.owlapi.model.OWLOntologyManager;


/**
 * Converts an ontology and a query into a set of clauses.
 */

public class DLliteParser {

	private OWLOntology ontology;

	/**
	 * Reads an ontology from the file specified by 'path' and
	 * returns a list of clauses representing the ontology.
	 * @param path the ontology to be converted.
	 * @return a set of clauses representing the ontology.
	 * @throws OWLException
	 */
	public ArrayList<PI> getAxioms(String path) throws OWLException
	{
		//Create ontology manager and load ontology (OWL API)
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		IRI physicalURI = IRI.create(path);
        ontology = manager.loadOntologyFromOntologyDocument(physicalURI);
        System.err.println(ontology.getAxiomCount());
        for (OWLAxiom oa: ontology.getAxioms())
        {
        	System.err.println(oa);
        }
        OWLAxioms oa = new OWLAxioms();
        //Normalize ontology (HermiT)
        OWLNormalization normalization = new OWLNormalization(manager.getOWLDataFactory(), oa, 0);
        normalization.processOntology(ontology);
        System.err.println(oa.m_classes.size());
        
        //Clausify ontology
        DLliteClausifier clausification = new DLliteClausifier();
        ArrayList<PI> axioms = clausification.getAxioms(oa);

        //Remove ontology from the ontology manager
        manager.removeOntology(ontology);

		return axioms;
	}

	/**
	 * Reads a query from the file specified by 'path' and
	 * returns a clause representing the query (based on ANTLR).
	 * @param path the query to be converted.
	 * @return a clause representing the query.
	 * @throws Exception
	 */
	public Clause getQuery(String path) throws Exception{

		BufferedReader reader = new BufferedReader(new FileReader(path));

		String input;
		do
			input = reader.readLine();
		while(input.indexOf("//") == 0);

		QueriesParser parser;
		byte currentBytes[] = input.getBytes();
		ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(currentBytes);
		ANTLRInputStream inputst = null;

		try {
			inputst = new ANTLRInputStream(byteArrayInputStream);
		} catch (IOException e) {
			e.printStackTrace(System.err);
			return null;
		}

		QueriesLexer lexer = new QueriesLexer(inputst);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		parser = new QueriesParser(tokens);

		try {
			parser.parse();
		} catch (Exception e) {
			return null;
		}

		if ((parser.getErrors().size() == 0) && (lexer.getErrors().size() == 0))
			return parser.getQuery();
		else
			return null;
	}

	/**
	 * Reads a query from the file specified by 'path' and
	 * returns a clause representing the query (based on ANTLR).
	 * @param path the query to be converted.
	 * @return a clause representing the query.
	 * @throws Exception
	 */
	public ArrayList<Clause> getQueryArrayList(String path) throws Exception{

		ArrayList<Clause> result = new ArrayList<Clause>();

		BufferedReader reader = new BufferedReader(new FileReader(path));

		ArrayList<String> inputList = new ArrayList<String>();
		String line;
		int i = 1;

		while ( (line = reader.readLine()) != null ) {

//			System.out.println(i++ + ": " + line);

			line = line.replace('^', ',');
			line = line.replace("(X0", "(?0");
			line = line.replace("(X1", "(?1");
			line = line.replace("(X2", "(?2");
			line = line.replace("(X3", "(?3");
			line = line.replace("(X4", "(?4");
			line = line.replace("(X500", "(?500");
			line = line.replace("(X501", "(?501");
			line = line.replace("(X502", "(?502");
			line = line.replace("(X503", "(?503");
			line = line.replace("(X504", "(?504");

			line = line.replace("X0)", "?0)");
			line = line.replace("X1)", "?1)");
			line = line.replace("X2)", "?2)");
			line = line.replace("X3)", "?3)");
			line = line.replace("X4)", "?4)");
			line = line.replace("X500)", "?500)");
			line = line.replace("X501)", "?501)");
			line = line.replace("X502)", "?502)");
			line = line.replace("X503)", "?503)");
			line = line.replace("X504)", "?504)");

			line = line.replace("Q1(", "Q(");
			line = line.replace("Q2(", "Q(");
			line = line.replace("Q3(", "Q(");
			line = line.replace("Q4(", "Q(");
			line = line.replace("Q5(", "Q(");
			line = line.replace( ":-", "<-" );
			line = line.replace( "?A0", "?0" );
			line = line.replace( "?A1", "?1" );
			line = line.replace( "?A2", "?2" );
			line = line.replace( "?A3", "?3" );
			line = line.replace( "?A4", "?4" );
			line = line.replace( "?A5", "?5" );
			line = line.replace( "?U0", "?50" );
			line = line.replace( "?U1", "?51" );
			line = line.replace( "?U2", "?52" );
			line = line.replace( "?U3", "?53" );
			line = line.replace( "?U4", "?54" );
			line = line.replace( "?U5", "?55" );

			line = line.replace( ", ", "," );
			line = line.replace( ".", "" );

			inputList.add(line);
		}

		i = 1;
		for ( String input : inputList ) {

//			System.out.println( i++ + ": " + input );

			if ( input.startsWith("//") || input.equals("") )
				continue;

			QueriesParser parser;
			byte currentBytes[] = input.getBytes();
			ByteArrayInputStream byteArrayInputStream = new ByteArrayInputStream(currentBytes);
			ANTLRInputStream inputst = null;

			try {
				inputst = new ANTLRInputStream(byteArrayInputStream);
			} catch (IOException e) {
				e.printStackTrace(System.err);
				return null;
			}

			QueriesLexer lexer = new QueriesLexer(inputst);
			CommonTokenStream tokens = new CommonTokenStream(lexer);
			parser = new QueriesParser(tokens);

			try {
				parser.parse();
			} catch (Exception e) {
				return null;
			}

			if ((parser.getErrors().size() == 0) && (lexer.getErrors().size() == 0)) {
				Clause c = parser.getQuery();
			 	result.add(c);
			}
			else
				System.out.println( input );

		}

		return result;
	}

	public int getNumberOfAxioms(){
	    return ontology == null? null: ontology.getAxioms().size();
	}

	public int getNumberOfConcepts(){
		return ontology == null? null: ontology.getClassesInSignature().size();
	}

	public int getNumberOfRoles(){
		return ontology == null? null: ontology.getObjectPropertiesInSignature().size();
	}

}
