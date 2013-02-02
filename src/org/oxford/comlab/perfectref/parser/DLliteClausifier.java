package org.oxford.comlab.perfectref.parser;

import java.util.ArrayList;

import org.oxford.comlab.perfectref.rewriter.PI;
import org.semanticweb.HermiT.owlapi.structural.OwlNormalization;
import org.semanticweb.owl.model.OWLClass;
import org.semanticweb.owl.model.OWLDescription;
import org.semanticweb.owl.model.OWLIndividualAxiom;
import org.semanticweb.owl.model.OWLObjectAllRestriction;
import org.semanticweb.owl.model.OWLObjectComplementOf;
import org.semanticweb.owl.model.OWLObjectPropertyExpression;
import org.semanticweb.owl.model.OWLObjectSomeRestriction;

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
	public ArrayList<PI> getAxioms(OwlNormalization normalization)
	{
		axioms = new ArrayList<PI>();

        //Facts
//		for(OWLIndividualAxiom axiom: normalization.getFacts())
//			System.err.println("Ignoring invalid individual axiom: " + axiom.toString());

        //Role inclusions
        for(OWLObjectPropertyExpression[] axiom: normalization.getObjectPropertyInclusions())
			addClauses(axiom);

		//Concept inclusions
        for(OWLDescription[] axiom: normalization.getConceptInclusions())
			addClauses(axiom);

        return axioms;
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

	/**
	 * Transforms a concept inclusion into a set of DLlite axioms.
	 *
	 * @param axiom the axiom to be converted.
	 */
	private void addClauses(OWLDescription[] axiom)
	{
		if(isValidClassInclusion(axiom)){

			//\forall R.A (valid universal quantification axiom)
			//4: \E P  -> A
			//7: \E P- -> A
			if(axiom.length == 1 && axiom[0] instanceof OWLObjectAllRestriction){
				String role = ((OWLObjectAllRestriction) axiom[0]).getProperty().getNamedProperty().toString();
				String fillerName = ((OWLObjectAllRestriction) axiom[0]).getFiller().toString();
				if(!((OWLObjectAllRestriction) axiom[0]).getProperty().toString().contains("InverseOf"))
					//7: \E R- -> A
					axioms.add(new PI(7, role, fillerName));
				else
					//4: \E R -> A
					axioms.add(new PI(4, role, fillerName));
			}
			else{
				ArrayList<OWLDescription> rule = new ArrayList<OWLDescription>();

				//Create an ArrayList of OWLDescription objects in which the head atom is in the first element
				for(OWLDescription atom: axiom)
					if(atom instanceof OWLObjectComplementOf || atom instanceof OWLObjectAllRestriction)
						rule.add(atom);
					else
						rule.add(0, atom);
				OWLDescription head = rule.get(0);
				OWLDescription body = rule.get(1).getComplementNNF();

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
					else if(body instanceof OWLObjectSomeRestriction){
						OWLDescription filler = ((OWLObjectSomeRestriction) body).getFiller();
						OWLObjectPropertyExpression property = ((OWLObjectSomeRestriction) body).getProperty();
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
				else if(head instanceof OWLObjectSomeRestriction){
					OWLDescription filler = ((OWLObjectSomeRestriction) head).getFiller();
					OWLObjectPropertyExpression property = ((OWLObjectSomeRestriction) head).getProperty();

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
							else if(body instanceof OWLObjectSomeRestriction){
								OWLDescription fillerB = ((OWLObjectSomeRestriction) body).getFiller();
								OWLObjectPropertyExpression propertyB = ((OWLObjectSomeRestriction) body).getProperty();
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
						else if(body instanceof OWLObjectSomeRestriction){
							OWLDescription fillerB = ((OWLObjectSomeRestriction) body).getFiller();
							OWLObjectPropertyExpression propertyB = ((OWLObjectSomeRestriction) body).getProperty();
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
						else if(body instanceof OWLObjectSomeRestriction){
							OWLDescription fillerB = ((OWLObjectSomeRestriction) body).getFiller();
							OWLObjectPropertyExpression propertyB = ((OWLObjectSomeRestriction) body).getProperty();
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
					else if(body instanceof OWLObjectSomeRestriction){
						OWLDescription fillerB = ((OWLObjectSomeRestriction) body).getFiller();
						OWLObjectPropertyExpression propertyB = ((OWLObjectSomeRestriction) body).getProperty();
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
	private boolean isValidClassInclusion(OWLDescription[] axiom){
		int i = 0;

		//T \implies \forall R.C
		if(axiom.length == 1 && axiom[0] instanceof OWLObjectAllRestriction)
			return true;

		if(axiom.length != 2)
			return false;

		for(OWLDescription atom: axiom){

			// Checking that each atom is of valid form
			if(!(atom instanceof OWLClass ||
				 atom instanceof OWLObjectComplementOf ||
				 atom instanceof OWLObjectSomeRestriction ||
				 atom instanceof OWLObjectAllRestriction))
				return false;

			// Counting occurrences of negated literals to verify Hornness
			if( atom instanceof OWLObjectComplementOf ||
				atom instanceof OWLObjectAllRestriction)
				i++;
		}

		// Checking Hornness
		return axiom.length == i+1;
	}
}
