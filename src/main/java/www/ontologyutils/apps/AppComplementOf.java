package www.ontologyutils.apps;

import java.io.File;
import java.util.stream.Collectors;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;

import www.ontologyutils.normalization.NormalForm;
import www.ontologyutils.toolbox.Utils;

public class AppComplementOf {
	private OWLOntology ontology;
	private String ontologyName;

	public AppComplementOf(String ontologyFilePath) {

		File ontologyFile = new File(ontologyFilePath);

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		IRI ontologyIRI = IRI.create(ontologyFile); 

		try {
			ontology = manager.loadOntologyFromOntologyDocument(ontologyIRI);
			this.ontologyName = ontology.getOntologyID().getOntologyIRI().get().toString();
			System.out.println("Ontology " + ontologyName + " loaded.");
		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
			System.exit(1);
		}
	}

	private void runNaive() {
        	// get all tbox axiom
        	Set<OWLAxiom> tboxAxioms = this.ontology.tboxAxioms(Imports.EXCLUDED).collect(Collectors.toSet());

        	// iterate each axiom
        	tboxAxioms.forEach(axiom -> {
            	try {
                	// determine if axiom is of type SubClassOf
                	if (axiom.isOfType(AxiomType.SUBCLASS_OF)) {
                    	// get left and right expressions (SubClass -> SuperClass)
                    	OWLClassExpression left = ((OWLSubClassOfAxiom) axiom).getSubClass();
                    	OWLClassExpression right = ((OWLSubClassOfAxiom) axiom).getSuperClass();

						
                    	// check if axiom is of (atom, negation atom)
                    	if (NormalForm.complementExpression(left, right)) {
							System.out.println(axiom.toString());
                   	 	} else {
                       	 	throw new Exception();
                    	}
                	}
            	} catch (Exception e) {

            	}
        	});
	}

	/**
	 * @param args
	 *            One argument must be given, corresponding to an OWL ontology file
	 *            path. E.g., run with the parameter resources/bodysystem.owl
	 */
	public static void main(String[] args) {
		AppComplementOf mApp = new AppComplementOf("resources/a-disjoint-b.owl");

		System.out.println("\nOriginal TBox");
		Utils.printTBox(mApp.ontology);

		///////////////////////////////////////////////////////////////////////////////////

		System.out.println("\nNAIVE NORMALIZATION");
		mApp.runNaive();

/*		System.out.println("\nTo rules");
		RuleGeneration rgn = new RuleGeneration(naive);
		rgn.getMapEntities().entrySet().stream()
			.forEach(e -> System.out.println(rgn.entityToRule(e.getKey())));
		naive.tboxAxioms(Imports.EXCLUDED).forEach(ax -> System.out.println(rgn.normalizedSubClassAxiomToRule(ax)));

		System.out.println("\nwhere");
		rgn.getMapEntities().entrySet().stream()
				.forEach(e -> System.out.println(e.getValue() + "\t\t" + Utils.pretty(e.getKey().toString())));

		///////////////////////////////////////////////////////////////////////////////////

		System.out.println("\nCONDOR NORMALIZATION");
		OWLOntology condor = mApp.runCondor();

		System.out.println("\nTo rules");
		RuleGeneration rgc = new RuleGeneration(condor);
		rgc.getMapEntities().entrySet().stream()
			.forEach(e -> System.out.println(rgc.entityToRule(e.getKey())));
		condor.tboxAxioms(Imports.EXCLUDED).forEach(ax -> System.out.println(rgc.normalizedSubClassAxiomToRule(ax)));

		System.out.println("\nwhere");
		rgc.getMapEntities().entrySet().stream()
				.forEach(e -> System.out.println(e.getValue() + "\t\t" + Utils.pretty(e.getKey().toString())));*/

		///////////////////////////////////////////////////////////////////////////////////

		System.out.println("\nFinished.");
	}
}
