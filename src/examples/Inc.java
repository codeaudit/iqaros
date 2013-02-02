import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Set;

import org.oxford.comlab.perfectref.parser.DLliteParser;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.PI;
import org.oxford.comlab.perfectref.rewriter.Substitution;
import org.oxford.comlab.perfectref.rewriter.Term;

import edu.ntua.image.Configuration;
import edu.ntua.image.Configuration.RedundancyEliminationStrategy;
import edu.ntua.image.datastructures.LabeledGraph;
import edu.ntua.image.incremental.Incremental;

public class Inc {

	private static final DLliteParser parser = new DLliteParser();

	private int orderedQueryIndex=0;

	public static void main(String[] args) throws Exception{

		String ontologyFile;
		String queryFile;
		ArrayList<PI> pis = new ArrayList<PI>();
		Incremental incremental = new Incremental();

		String path = System.getProperty("user.dir")+ "/dataset/Evaluation_ISWC'09/";
		path = path.replaceAll(" ", "%20");
		//run all Hector's Ontologies and queries
		runEvaluation(path);
		
		//run Martha's queries
//		runEvaluation2(System.getProperty("user.dir")+ "/dataset/Marthas/");

//
//		queryFile = System.getProperty("user.dir")+ "/dataset/Tests/queries.txt";
//		ontologyFile = "file:" + path + "Ontologies/A.owl";
//////
//		ArrayList<PI> tBoxAxioms = parser.getAxioms(ontologyFile);
//
//		Clause originalQuery = parser.getQuery(queryFile);
//		System.out.println("Original Query = " + originalQuery);
//		ArrayList<Clause> result = incremental.computeUCQRewriting(tBoxAxioms,originalQuery);
//
////		int i = 1;
////		for ( Clause c :result )
////			System.out.println( i++ + " : " + c);

	}
	
	private static void runEvaluation2(String path) throws Exception {
		String ontologyFile,queryPath="";

//		System.out.println( "Starting test for ontology P5X.owl");
		ontologyFile = "file:" + path + "Ontologies/P5X.owl";
		queryPath = path + "Queries/P5X/";
		runTest(ontologyFile,queryPath);
		
//		System.out.println( "Starting test for ontology A.owl");
		ontologyFile = "file:" + path + "Ontologies/A.owl";
		queryPath = path + "Queries/A/";
		runTest(ontologyFile,queryPath);
		
//		System.out.println( "Starting test for ontology AX.owl");
		ontologyFile = "file:" + path + "Ontologies/AX.owl";
		queryPath = path + "Queries/AX/";
		runTest(ontologyFile,queryPath);
		
//		System.out.println( "Starting test for ontology S.owl");
		ontologyFile = "file:" + path + "Ontologies/S.owl";
		queryPath = path + "Queries/S/";
		runTest(ontologyFile,queryPath);
		
//		System.out.println( "Starting test for ontology U.owl");
		ontologyFile = "file:" + path + "Ontologies/U.owl";
		queryPath = path + "Queries/U/";
		runTest(ontologyFile,queryPath);
		
//		System.out.println( "Starting test for ontology UX.owl");
		ontologyFile = "file:" + path + "Ontologies/UX.owl";
		queryPath = path + "Queries/UX/";
		runTest(ontologyFile,queryPath);
		
//		System.out.println( "Starting test for ontology V.owl");
		ontologyFile = "file:" + path + "Ontologies/V.owl";
		queryPath = path + "Queries/V/";
		runTest(ontologyFile,queryPath);		
	}

	private static void runEvaluation(String path) throws Exception {
		String ontologyFile,queryPath="";

		System.out.println( "Starting test for ontology V.owl");
		ontologyFile = "file:" + path + "Ontologies/V.owl";
		queryPath = path + "Queries/V/";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology P1.owl");
		ontologyFile = "file:" + path + "Ontologies/P1.owl";
		queryPath = path + "Queries/P1/";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology P5.owl");
		ontologyFile = "file:" + path + "Ontologies/P5.owl";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology P5X.owl");
		ontologyFile = "file:" + path + "Ontologies/P5X.owl";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology S.owl");
		ontologyFile = "file:" + path + "Ontologies/S.owl";
		queryPath = path + "Queries/S/";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology U.owl");
		ontologyFile = "file:" + path + "Ontologies/U.owl";
		queryPath = path + "Queries/U/";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology UX.owl");
		ontologyFile = "file:" + path + "Ontologies/UX.owl";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology A.owl");
		ontologyFile = "file:" + path + "Ontologies/A.owl";
		queryPath = path + "Queries/A/";
		runTest(ontologyFile,queryPath);

		System.out.println( "Starting test for ontology AX.owl");
		ontologyFile = "file:" + path + "Ontologies/AX.owl";
		runTest(ontologyFile,queryPath);
	}

	private static void runTest(String ontologyFile, String queryPath) throws Exception {
		long start=0,totalTime = 0;
		ArrayList<PI> tBoxAxioms = parser.getAxioms(ontologyFile);

		File queriesDir = new File( queryPath );
		File[] queries = queriesDir.listFiles();
		System.out.println( queriesDir );
		for( int i=0 ; i<queries.length ; i++ ) {
	        if( queries[i] == null )
	    	   // Either dir does not exist or is not a directory
	    	   return;
	        else if( !queries[i].toString().contains(".svn") ) {//&& !queries[i].toString().contains("QTB") ) {
	        	start = System.currentTimeMillis();
				new Incremental().computeUCQRewriting(tBoxAxioms,parser.getQuery(queries[i].toString()));
	    		/** OR, in order to run the evaluation using non-restricted subsumption */
//	    		Configuration c = new Configuration();
//	    		c.redundancyElimination=RedundancyEliminationStrategy.Full_Subsumption;
//	    		Incremental incremental = new Incremental( c );
//	    		incremental.computeUCQRewriting(tBoxAxioms,parser.getQuery(queries[i].toString()));
				totalTime+= (System.currentTimeMillis()-start);

	        }
		}
//		System.out.println( "Finished rewriting " + queries.length + " in " + totalTime + " ms" );
		System.out.println( totalTime );
	}
	

}