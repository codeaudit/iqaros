package org.oxford.comlab.perfectref.parser;

import java.util.ArrayList;
import java.util.Set;

import org.oxford.comlab.perfectref.rewriter.PI;

import org.semanticweb.owlapi.model.OWLClass;
//import org.semanticweb.owlapi.model.
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
//import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
//import org.semanticweb.owlapi.model;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLClassExpression;
//import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.HermiT.structural.OWLAxioms;
import org.semanticweb.HermiT.structural.OWLNormalization;

import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLException;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.reasoner.structural.StructuralReasoner;

public class DLliteClausifier {
	private int artificialRoleIndex = 0;
	private ArrayList<PI> axioms;

	/**
	 * Gets a set of normalized axioms and converts it into a set of DLlite axioms.
	 * We only consider concept inclusions and object property inclusions:
	 *
	 *  OWLSubClassAxiom
	 *  OWLEquivalentClassesAxiom
	 *  OWLObjectSubPropertyAxiom
	 *  OWLEquivalentObjectPropertiesAxiom
	 *  OWLObjectPropertyDomainAxiom
	 *  OWLObjectPropertyRangeAxiom
	 *  OWLInverseObjectPropertiesAxiom
	 *
	 * @param normalization the set of axioms to be converted.
	 * @return a set of clauses.
	 */
	public ArrayList<PI> getAxioms(OWLOntology normalization)
	{
		axioms = new ArrayList<PI>();

        //Facts
//		for(OWLIndividualAxiom axiom: normalization.getFacts())
//			System.err.println("Ignoring invalid individual axiom: " + axiom.toString());

        //Role inclusions
		Set<OWLAxiom> s = normalization.getTBoxAxioms(null);
		for (OWLAxiom a: s)
		{
			//a.
		}
		
		for (OWLObjectProperty a: normalization.getObjectPropertiesInSignature())
		{
			for (OWLSubObjectPropertyOfAxiom a1: normalization.getObjectSubPropertyAxiomsForSubProperty(a))
			{
				//a1.getObjectPropertiesInSignature();
				addClauses(a1);
			}
		}
		
		for (OWLClass c: normalization.getClassesInSignature())
		{
			for (OWLSubClassOfAxiom a1: normalization.getSubClassAxiomsForSubClass(c))
			{
				addClauses(a1);
			}
		}
		
        //for(OWLObjectPropertyExpression[] axiom: n.getObjectPropertyInclusions())
		//	addClauses(axiom);

		//Concept inclusions
        //for(OWLClassExpression[] axiom: normalization.getConceptInclusions())
		//	addClauses(axiom);

        return axioms;
	}

	
	public ArrayList<PI> getAxioms(OWLAxioms oa) {
		axioms = new ArrayList<PI>();
		for(OWLObjectPropertyExpression[] axiom: oa.m_simpleObjectPropertyInclusions)
			addClauses(axiom);
		//for(OWLObjectPropertyExpression[] axiom: oa.m_complexObjectPropertyInclusions)
		//	addClauses(axiom);
		
		for(OWLClassExpression[] axiom: oa.m_conceptInclusions)
		addClauses(axiom);
		// TODO Auto-generated method stub
		return axioms;
	}
	

	private void addClauses(OWLSubObjectPropertyOfAxiom axiom1)
	{
		OWLObjectPropertyExpression[] axiom = {axiom1.getSubProperty(), axiom1.getSuperProperty() };
		
		if(isValidObjectPropertyInclusion(axiom)){
			String role0 = axiom[0].getNamedProperty().toString();
			String role1 = axiom[1].getNamedProperty().toString();
			if((!axiom[0].toString().contains("InverseOf") && axiom[1].toString().contains("InverseOf")) ||
			   (axiom[0].toString().contains("InverseOf") && !axiom[1].toString().contains("InverseOf")))
				//11: R -> S-, R- -> S
				axioms.add(new PI(11, role0, role1));
			else if((axiom[0].toString().contains("InverseOf") && axiom[1].toString().contains("InverseOf")) ||
			       (!axiom[0].toString().contains("InverseOf") && !axiom[1].toString().contains("InverseOf")))
				//10: R -> S, R- -> S-
				axioms.add(new PI(10, role0, role1));
		}
		else{
//			System.err.print("ignoring role inclusion: ");
//        	for(int j=0; j<axiom.length; j++)
//				System.err.print(axiom[j].toString() + " ");
//            System.err.println();
		}
	}
	/**
	 * Converts an object property axiom into a DLlite axiom.
	 * We only consider object property inclusions of the form R(-) -> S(-)
	 * @param axiom the axiom to be converted
	 */
	private void addClauses(OWLObjectPropertyExpression[] axiom)
	{
		if(isValidObjectPropertyInclusion(axiom)){
			String role0 = axiom[0].getNamedProperty().toString();
			String role1 = axiom[1].getNamedProperty().toString();
			if((!axiom[0].toString().contains("InverseOf") && axiom[1].toString().contains("InverseOf")) ||
			   (axiom[0].toString().contains("InverseOf") && !axiom[1].toString().contains("InverseOf")))
				//11: R -> S-, R- -> S
				axioms.add(new PI(11, role0, role1));
			else if((axiom[0].toString().contains("InverseOf") && axiom[1].toString().contains("InverseOf")) ||
			       (!axiom[0].toString().contains("InverseOf") && !axiom[1].toString().contains("InverseOf")))
				//10: R -> S, R- -> S-
				axioms.add(new PI(10, role0, role1));
		}
		else{
//			System.err.print("ignoring role inclusion: ");
//        	for(int j=0; j<axiom.length; j++)
//				System.err.print(axiom[j].toString() + " ");
//            System.err.println();
		}
	}

	/**
	 * Verifies that the given object property inclusion is valid, i.e. that it consists of exactly two atoms, none of which is TopObjectProperty
	 * @param axiom
	 * @return
	 */
    private boolean isValidObjectPropertyInclusion(OWLObjectPropertyExpression[] axiom){
		return axiom.length == 2 && !axiom[0].toString().equals("TopObjectProperty") && !axiom[1].toString().equals("TopObjectProperty");
    }

    private void addClauses(OWLSubClassOfAxiom a1) 
	{
		// TODO Auto-generated method stub
    	OWLClassExpression sub = a1.getSubClass();
    	OWLClassExpression sup = a1.getSuperClass();
    	OWLClassExpression[] e = { sub, sup };
    	addClauses(e);
	}
	/**
	 * Transforms a concept inclusion into a set of DLlite axioms.
	 *
	 * @param axiom the axiom to be converted.
	 */
	private void addClauses(OWLClassExpression[] axiom)
	{
		if(isValidClassInclusion(axiom)){

			//\forall R.A (valid universal quantification axiom)
			//4: \E P  -> A
			//7: \E P- -> A
			if(axiom.length == 1 && axiom[0] instanceof OWLObjectAllValuesFrom){
				String role = ((OWLObjectAllValuesFrom) axiom[0]).getProperty().getNamedProperty().toString();
				String fillerName = ((OWLObjectAllValuesFrom) axiom[0]).getFiller().toString();
				if(!((OWLObjectAllValuesFrom) axiom[0]).getProperty().toString().contains("InverseOf"))
					//7: \E R- -> A
					axioms.add(new PI(7, role, fillerName));
				else
					//4: \E R -> A
					axioms.add(new PI(4, role, fillerName));
			}
			else{
				ArrayList<OWLClassExpression> rule = new ArrayList<OWLClassExpression>();

				//Create an ArrayList of OWLClassExpression objects in which the head atom is in the first element
				for(OWLClassExpression atom: axiom)
					if(atom instanceof OWLObjectComplementOf || atom instanceof OWLObjectAllValuesFrom)
						rule.add(atom);
					else
						rule.add(0, atom);
				OWLClassExpression head = rule.get(0);
				OWLClassExpression body = rule.get(1).getComplementNNF();

				String left, right;

				//head of the form: B
				//  1: A     -> B
				//  4: \E P  -> B
				//  7: \E P- -> B
				if(head instanceof OWLClass){

					right = ((OWLClass)head).toString();

					//body of the form: A
					if(body instanceof OWLClass){
						left = ((OWLClass)body).toString();
						//1: A -> B
						axioms.add(new PI(1, left, right));
					}

					//body of the form: \E R
					else if(body instanceof OWLObjectSomeValuesFrom){
						OWLClassExpression filler = ((OWLObjectSomeValuesFrom) body).getFiller();
						OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom) body).getProperty();
						left = property.getNamedProperty().toString();

						if(filler.toString().equals("ObjectComplementOf(Nothing)")){
							//R of the form: P-
							if(property.toString().contains("InverseOf"))
								//7: \E P- -> B
								axioms.add(new PI(7, left, right));
							else
								//4: \E P -> B
								axioms.add(new PI(4, left, right));
						}
						else{
							System.err.print("ignoring invalid concept inclusion: ");
				       		for(int j=0; j<axiom.length; j++)
								System.err.print(axiom[j].toString() + " ");
				           	System.err.println();
						}
					}
				}

				//head of the form: \E R.C
				else if(head instanceof OWLObjectSomeValuesFrom){
					OWLClassExpression filler = ((OWLObjectSomeValuesFrom) head).getFiller();
					OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom) head).getProperty();

					right = property.getNamedProperty().toString();

					//head of the form: \E R
					//2: A     -> \E P
					//3: A     -> \E P-
					//5: \E P  -> \E S
					//6: \E P  -> \E S-
					//8: \E P- -> \E S
					//9: \E P- -> \E S-
					if(filler.toString().equals("Thing")){

						//R of the form: P-
						//3: A     -> \E P-
						//6: \E P  -> \E S-
						//9: \E P- -> \E S-
						if(property.toString().contains("InverseOf")){

							//body of the form: C
							if(body instanceof OWLClass){
								left = ((OWLClass)body).toString();
								//3: A -> \E P-
								axioms.add(new PI(3, left, right));
							}

							//body of the form: \E R
							else if(body instanceof OWLObjectSomeValuesFrom){
								OWLClassExpression fillerB = ((OWLObjectSomeValuesFrom) body).getFiller();
								OWLObjectPropertyExpression propertyB = ((OWLObjectSomeValuesFrom) body).getProperty();
								left = propertyB.getNamedProperty().toString();

								//No qualified existential quantification in the body
								if(fillerB.toString().equals("ObjectComplementOf(Nothing)")){
									//R of the form: P-
									if(propertyB.toString().contains("InverseOf"))
										//9: \E P- -> \E S-
										axioms.add(new PI(9, left, right));
									else
										//6: \E P -> \E S-
										axioms.add(new PI(6, left, right));
								}
								else{
									System.err.print("ignoring invalid concept inclusion: ");
						       		for(int j=0; j<axiom.length; j++)
										System.err.print(axiom[j].toString() + " ");
						           	System.err.println();
								}
							}
						} else //body of the form: C
						if(body instanceof OWLClass){
							left = ((OWLClass)body).toString();
							//2: A -> \E P
							axioms.add(new PI(2, left, right));
						}

						//body of the form: \E R
						else if(body instanceof OWLObjectSomeValuesFrom){
							OWLClassExpression fillerB = ((OWLObjectSomeValuesFrom) body).getFiller();
							OWLObjectPropertyExpression propertyB = ((OWLObjectSomeValuesFrom) body).getProperty();
							left = propertyB.getNamedProperty().toString();

							//No qualified existential quantification in the body
							if(fillerB.toString().equals("ObjectComplementOf(Nothing)")){
								//R of the form: P-
								if(propertyB.toString().contains("InverseOf"))
									//8: \E P-  -> \E S
									axioms.add(new PI(8, left, right));
								else
									//5: \E P  -> \E S
									axioms.add(new PI(5, left, right));
							}
							else{
								System.err.print("ignoring invalid concept inclusion: ");
						   		for(int j=0; j<axiom.length; j++)
									System.err.print(axiom[j].toString() + " ");
						       	System.err.println();
							}
						}
					} else //R of the form: P-
					if(property.toString().contains("InverseOf")){
						//body of the form: A
						if(body instanceof OWLClass){
							String auxRole = "AUX$" + artificialRoleIndex++;
							//3:  A       -> \E AUXi-
							//4:  \E AUXi -> A
							//10: AUXi    -> S
							axioms.add(new PI(3,((OWLClass)body).toString(), auxRole));
							axioms.add(new PI(4, auxRole, filler.toString()));
							axioms.add(new PI(10, auxRole, property.getNamedProperty().toString()));
						}

						//body of the form: \E R
						else if(body instanceof OWLObjectSomeValuesFrom){
							OWLClassExpression fillerB = ((OWLObjectSomeValuesFrom) body).getFiller();
							OWLObjectPropertyExpression propertyB = ((OWLObjectSomeValuesFrom) body).getProperty();
							left = propertyB.getNamedProperty().toString();

							if(fillerB.toString().equals("ObjectComplementOf(Nothing)")){
								//R of the form: P-
								if(propertyB.toString().contains("InverseOf")){
									String auxRole = "AUX$" + artificialRoleIndex++;
									axioms.add(new PI(9, propertyB.getNamedProperty().toString(), auxRole));
									axioms.add(new PI(4, auxRole, filler.toString()));
									axioms.add(new PI(10, auxRole, property.getNamedProperty().toString()));
								}
								//R of the form: P
								else{
									String auxRole = "AUX$" + artificialRoleIndex++;
									axioms.add(new PI(6, propertyB.getNamedProperty().toString(), auxRole));
									axioms.add(new PI(4, auxRole, filler.toString()));
									axioms.add(new PI(10, auxRole, property.getNamedProperty().toString()));
								}
							}
							else{
								System.err.print("ignoring invalid concept inclusion: ");
					       		for(int j=0; j<axiom.length; j++)
									System.err.print(axiom[j].toString() + " ");
					           	System.err.println();
							}
						}
					} else //body of the form: C
					if(body instanceof OWLClass){
						String auxRole = "AUX$" + artificialRoleIndex++;
						axioms.add(new PI(2,((OWLClass)body).toString(), auxRole));
						axioms.add(new PI(7, auxRole, filler.toString()));
						axioms.add(new PI(10, auxRole, property.getNamedProperty().toString()));
					}

					//body of the form: \E R
					else if(body instanceof OWLObjectSomeValuesFrom){
						OWLClassExpression fillerB = ((OWLObjectSomeValuesFrom) body).getFiller();
						OWLObjectPropertyExpression propertyB = ((OWLObjectSomeValuesFrom) body).getProperty();
						left = propertyB.getNamedProperty().toString();

						if(fillerB.toString().equals("ObjectComplementOf(Nothing)")){
							//R of the form: P-
							if(propertyB.toString().contains("InverseOf")){
								String auxRole = "AUX$" + artificialRoleIndex++;
								axioms.add(new PI(8, propertyB.getNamedProperty().toString(), auxRole));
								axioms.add(new PI(7, auxRole, filler.toString()));
								axioms.add(new PI(10, auxRole, property.getNamedProperty().toString()));
							}
							//R of the form: P
							else{
								String auxRole = "AUX$" + artificialRoleIndex++;
								axioms.add(new PI(5, propertyB.getNamedProperty().toString(), auxRole));
								axioms.add(new PI(7, auxRole, filler.toString()));
								axioms.add(new PI(10, auxRole, property.getNamedProperty().toString()));
							}
						}
						else{
							System.err.print("ignoring invalid concept inclusion: ");
					   		for(int j=0; j<axiom.length; j++)
								System.err.print(axiom[j].toString() + " ");
					       	System.err.println();
						}
					}
				}
			}
		}
		else{
       		System.err.print("ignoring invalid concept inclusion: ");
       		for(int j=0; j<axiom.length; j++)
				System.err.print(axiom[j].toString() + " ");
           	System.err.println();
		}
	}

	/**
	 * Verifies that a given class inclusion is valid
	 * @param axiom
	 * @return
	 */
	private boolean isValidClassInclusion(OWLClassExpression[] axiom){
		int i = 0;

		//T \implies \forall R.C
		if(axiom.length == 1 && axiom[0] instanceof OWLObjectAllValuesFrom)
			return true;

		if(axiom.length != 2)
			return false;

		for(OWLClassExpression atom: axiom){

			// Checking that each atom is of valid form
			if(!(atom instanceof OWLClass ||
				 atom instanceof OWLObjectComplementOf ||
				 atom instanceof OWLObjectSomeValuesFrom ||
				 atom instanceof OWLObjectAllValuesFrom))
				return false;

			// Counting occurrences of negated literals to verify Hornness
			if( atom instanceof OWLObjectComplementOf ||
				atom instanceof OWLObjectAllValuesFrom)
				i++;
		}

		// Checking Hornness
		return axiom.length == i+1;
	}





	
}
