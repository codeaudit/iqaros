import java.util.ArrayList;
import java.io.File;
import org.oxford.comlab.perfectref.parser.DLliteParser;
import org.oxford.comlab.perfectref.rewriter.Clause;
import org.oxford.comlab.perfectref.rewriter.PI;

import edu.ntua.image.Configuration;
import edu.ntua.image.Configuration.RedundancyEliminationStrategy;
import edu.ntua.image.incremental.Incremental;

public class MyIqarosCLI {

	private static final DLliteParser parser = new DLliteParser();

	private int orderedQueryIndex=0;

	public static void main(String[] args) throws Exception{
        if(args.length == 2){
            String ontologyFile = args[0];
            String queryFile = args[1];
        			
            String ontologyURI = new File(ontologyFile).toURI().toString();
		
            ArrayList<PI> tBoxAxioms = new ArrayList<PI>();
            
            System.out.println("/*");

            tBoxAxioms = parser.getAxioms(ontologyURI);

            Clause originalQuery = parser.getQuery(queryFile);
            System.out.println("Original Query = " + originalQuery);
            Incremental incremental = new Incremental();
            ArrayList<Clause> result = incremental.computeUCQRewriting(tBoxAxioms,originalQuery);

            System.out.println("*/");

            for(Clause r : result){
                System.out.println(r);
            }

            /** OR, in order to run the evaluation using non-restricted subsumption */
            //		Configuration c = new Configuration();
            //		c.redundancyElimination=RedundancyEliminationStrategy.Full_Subsumption;
            //		Incremental incremental = new Incremental( c );
            //		ArrayList<Clause> result =
            //		incremental.computeUCQRewriting(tBoxAxioms,originalQuery);
        }else{
            System.err.println("Usage: java -jar iqaros-cli.jar ontology.owl query.cq");
            System.exit(-1);
        }
	}

}
