package examples;
import java.util.ArrayList;

import org.oxford.comlab.perfectref.parser.DLliteParser;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.PI;

import edu.ntua.image.Configuration;
import edu.ntua.image.Configuration.RedundancyEliminationStrategy;
import edu.ntua.image.incremental.Incremental;

public class IncSingleEx {

	private static final DLliteParser parser = new DLliteParser();

	private int orderedQueryIndex=0;

	public static void main(String[] args) throws Exception{

		String ontologyFile;
		String queryFile;
		ArrayList<PI> tBoxAxioms = new ArrayList<PI>();

		String path = System.getProperty("user.dir")+ "/dataset/Evaluation_ISWC'09/";

		queryFile = System.getProperty("user.dir")+ "/dataset/Tests/queries.txt";
		ontologyFile = "file:" + System.getProperty("user.dir") + "/dataset/Tests/SimpleSub.owl";
//		ontologyFile = "file:" + path + "Ontologies/P5X.owl";

		tBoxAxioms = parser.getAxioms(ontologyFile);

		Clause originalQuery = parser.getQuery(queryFile);
		System.out.println("Original Query = " + originalQuery);
		Incremental incremental = new Incremental();
		ArrayList<Clause> result = incremental.computeUCQRewriting(tBoxAxioms,originalQuery);
		/** OR, in order to run the evaluation using non-restricted subsumption */
//		Configuration c = new Configuration();
//		c.redundancyElimination=RedundancyEliminationStrategy.Full_Subsumption;
//		Incremental incremental = new Incremental( c );
//		ArrayList<Clause> result = incremental.computeUCQRewriting(tBoxAxioms,originalQuery);
	}

}