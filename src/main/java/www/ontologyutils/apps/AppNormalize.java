package www.ontologyutils.apps;

import java.io.File;
import java.util.stream.Stream;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.parameters.Imports;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import www.ontologyutils.normalization.Normalization;
import www.ontologyutils.normalization.NormalizationTools;
import www.ontologyutils.rules.RuleGeneration;
import www.ontologyutils.toolbox.FreshAtoms;
import www.ontologyutils.toolbox.Utils;

public class AppNormalize {
	private OWLOntology ontology;
	private String ontologyName;

	public AppNormalize(String ontologyFilePath) {

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

	private OWLOntology runCondor() {
		FreshAtoms.resetFreshAtomsEquivalenceAxioms(); // optional; for verification purpose

		OWLOntology copy = Utils.newEmptyOntology();
		copy.addAxioms(this.ontology.axioms());

		Stream<OWLAxiom> tBoxAxioms = copy.tboxAxioms(Imports.EXCLUDED);
		tBoxAxioms.forEach((ax) -> {
			copy.remove(ax);
			copy.addAxioms(NormalizationTools.asSubClassOfAxioms(ax));
		});

		System.out.println("\nCondor Normalized TBox");
		OWLOntology condor = null;
		condor = Normalization.normalizeCondor(copy);

		condor.tboxAxioms(Imports.EXCLUDED).forEach(ax -> System.out.println(Utils.pretty("-- " + ax.toString())));

		// check every axiom of the original ontology is entailed in condor
		OWLReasoner reasoner = Utils.getHermitReasoner(condor);
		assert (this.ontology.axioms().allMatch(ax -> reasoner.isEntailed(ax)));
		// check every axiom of condor is entailed in the copy of the original ontology
		// with extended signature
		copy.addAxioms(FreshAtoms.getFreshAtomsEquivalenceAxioms());
		OWLReasoner reasonerBis = Utils.getHermitReasoner(copy);
		assert (condor.axioms().allMatch(ax -> reasonerBis.isEntailed(ax)));

		return condor;
	}

	private OWLOntology runNaive() {
		FreshAtoms.resetFreshAtomsEquivalenceAxioms(); // optional; for verification purpose

		OWLOntology copy = Utils.newEmptyOntology();
		copy.addAxioms(this.ontology.axioms());

		Stream<OWLAxiom> tBoxAxioms = copy.tboxAxioms(Imports.EXCLUDED);
		tBoxAxioms.forEach((ax) -> {
			copy.remove(ax);
			copy.addAxioms(NormalizationTools.asSubClassOfAxioms(ax));
		});

		System.out.println("\nNaive Normalized TBox");
		OWLOntology naive = null;
		naive = Normalization.normalizeNaive(copy);

		naive.tboxAxioms(Imports.EXCLUDED).forEach(ax -> System.out.println(Utils.pretty("-- " + ax.toString())));

		// check every axiom of the original ontology is entailed in naive
		OWLReasoner reasoner = Utils.getHermitReasoner(naive);
		assert (this.ontology.axioms().allMatch(ax -> reasoner.isEntailed(ax)));
		// check every axiom of naive is entailed in the copy of the original ontology
		// with extended signature
		copy.addAxioms(FreshAtoms.getFreshAtomsEquivalenceAxioms());
		OWLReasoner reasonerBis = Utils.getHermitReasoner(copy);
		assert (naive.axioms().allMatch(ax -> reasonerBis.isEntailed(ax)));

		return naive;
	}

	/**
	 * @param args
	 *            One argument must be given, corresponding to an OWL ontology file
	 *            path. E.g., run with the parameter resources/bodysystem.owl
	 */
	public static void main(String[] args) {
		AppNormalize mApp = new AppNormalize(args[0]);

		System.out.println("\nOriginal TBox");
		Utils.printTBox(mApp.ontology);

		///////////////////////////////////////////////////////////////////////////////////

		System.out.println("\nNAIVE NORMALIZATION");
		OWLOntology naive = mApp.runNaive();

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
