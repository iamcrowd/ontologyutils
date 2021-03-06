package www.ontologyutils.collective;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ThreadLocalRandom;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;

import www.ontologyutils.collective.BinaryVoteFactory.BinaryVote;
import www.ontologyutils.collective.PreferenceFactory.Preference;
import www.ontologyutils.refinement.AxiomWeakener;
import www.ontologyutils.toolbox.Utils;

/**
 * 
 * @author nico
 * 
 *         Daniele Porello, Nicolas Troquard, Rafael Peñaloza, Roberto
 *         Confalonieri, Pietro Galliani, and Oliver Kutz. Two Approaches to
 *         Ontology Aggregation Based on Axiom Weakening. In 27th International
 *         Joint Conference on Artificial Intelligence and 23rd European
 *         Conference on Artificial Intelligence (IJCAI-ECAI 2018).
 *         International Joint Conferences on Artificial Intelligence
 *         Organization, 2018, pages 1942-1948.
 * 
 */
public class TurnBasedMechanism {

	private List<OWLAxiom> agenda;
	private List<Preference> preferences;
	private List<BinaryVote> approvals;
	private OWLOntology referenceOntology;
	private int numVoters;

	private boolean verbose = false;

	private void log(String message) {
		if (verbose) {
			System.out.print(message);
		}
	}

	/**
	 * @param verbose a boolean, true for verbose logging, and false for silent
	 *                execution.
	 * @return the current instance.
	 */
	public TurnBasedMechanism setVerbose(boolean verbose) {
		this.verbose = verbose;
		return this;
	}

	/**
	 * @param agenda            a list of axioms.
	 * @param preferences       a list of preferences over the agenda, one for every
	 *                          intended voter.
	 * @param approvals         a list of binary votes over the agenda, one for
	 *                          every intended voter.
	 * @param referenceOntology a consistent reference ontology.
	 */
	public TurnBasedMechanism(List<OWLAxiom> agenda, List<Preference> preferences, List<BinaryVote> approvals,
			OWLOntology referenceOntology) {
		if (preferences.stream().anyMatch(p -> !p.getAgenda().equals(agenda))) {
			throw new IllegalArgumentException("The preferences must be built from the agenda in parameter.");
		}
		if (approvals.stream().anyMatch(a -> !a.getAgenda().equals(agenda))) {
			throw new IllegalArgumentException(
					"The binary votes in the approvals must be built from the agenda in parameter.");
		}
		if (preferences.size() != approvals.size()) {
			throw new IllegalArgumentException("There must be as many preferences as approvals.");
		}
		if (!Utils.isConsistent(referenceOntology)) {
			throw new IllegalArgumentException("The reference ontology must be consistent.");
		}
		this.referenceOntology = referenceOntology;

		for (int i = 0; i < numVoters; i++) {
			for (int rank = 1; rank < agenda.size(); rank++) {
				int approvalRank = approvals.get(i).getVote(preferences.get(i).get(rank));
				int approvalRankPlusOne = approvals.get(i).getVote(preferences.get(i).get(rank + 1));
				if (approvalRank < approvalRankPlusOne) {
					throw new IllegalArgumentException(
							"Approvals must be coherent with preferences. Here : in preference " + i + " axiom ranked "
									+ (rank + 1) + " has better approval than axiom ranked " + rank);
				}
			}
		}
		this.approvals = approvals;
		this.agenda = agenda;
		this.preferences = preferences;
		this.numVoters = preferences.size();
	}

	/**
	 * @param axioms a list of axioms.
	 * @param pref   a preference over {@code axioms}.
	 * @param vote   a binary vote over {@code axioms}.
	 * @return The preferred axiom in {@code axioms} according to {@code pref} that
	 *         is approved in {@code vote}. Sometimes it returns {@code null}.
	 */
	private OWLAxiom favorite(List<OWLAxiom> axioms, Preference pref, BinaryVote vote) {
		List<OWLAxiom> approvedAxioms = new ArrayList<>();
		for (OWLAxiom a : axioms) {
			if (vote.getVote(a) == 1) {
				approvedAxioms.add(a);
			}
		}
		OWLAxiom result = null;
		if (!approvedAxioms.isEmpty()) {
			result = approvedAxioms.get(0);
		} else {
			return null;
		}
		assert (result != null);
		for (OWLAxiom a : approvedAxioms) {
			if (pref.getRank(a) < pref.getRank(result)) {
				result = a;
			}
		}
		return result;
	}

	/**
	 * @param ax
	 * @return true if axiom {code ax} is approved in at least one of the binary
	 *         votes in {@code approvals}.
	 */
	private boolean hasSupport(OWLAxiom ax) {
		return approvals.stream().anyMatch(bv -> (bv.getVote(ax) == 1));
	}

	public enum Initialization {
		EMPTY, REFERENCE, REFERENCE_WITH_SUPPORT;
	}

	/**
	 * @param initizalization
	 * @return the reference ontology, the accepted subset of the reference
	 *         ontology, or an empty ontology depending on {@code initialization}
	 *         parameter.
	 */
	private OWLOntology init(Initialization initialization) {
		OWLOntology result = null;

		switch (initialization) {
		case EMPTY:
			result = Utils.newEmptyOntology();
			break;
		case REFERENCE:
			result = referenceOntology;
			break;
		case REFERENCE_WITH_SUPPORT:
			result = referenceOntology;
			for (OWLAxiom ax : referenceOntology.axioms().collect(Collectors.toSet())) {
				if (!hasSupport(ax)) {
					result.remove(ax);
				}
			}
			break;
		}

		return result;
	}

	/**
	 * @param initialization the mechanism will be initialized with either
	 *                       <ul>
	 *                       <li>the reference ontology when using
	 *                       {@code REFERENCE},</li>
	 *                       <li>the accepted subset of the reference ontology when
	 *                       using {@code REFERENCE_WITH_SUPPORT},</li>
	 *                       <li>or an empty ontology when using {@code EMPTY}.</li>
	 *                       </ul>
	 * @return the ontology resulting from the turn based mechanism.
	 */
	public OWLOntology get(Initialization initialization) {
		OWLOntology result = init(initialization);

		List<OWLAxiom> currentAgenda = new ArrayList<>();
		currentAgenda.addAll(agenda.stream().collect(Collectors.toList()));

		// trim the current agenda from the axioms already in the reference ontology
		result.axioms().forEach(a -> currentAgenda.remove(a));

		// init turn
		int currentVoter = 0;
		Set<Integer> haveGivenUp = new HashSet<>();

		while (!currentAgenda.isEmpty() && haveGivenUp.size() < numVoters) {
			log("\nCurrent voter: " + (currentVoter + 1));
			// currentVoter's favorite axiom still in the current agenda
			OWLAxiom favorite = favorite(currentAgenda, preferences.get(currentVoter), approvals.get(currentVoter));

			if (favorite == null) {
				// currentVoter does not approve of any axioms remaining in currentAgenda
				haveGivenUp.add(currentVoter);
				log("\nVoter " + (currentVoter + 1) + " gives up!");
				currentVoter = (currentVoter + 1) % numVoters;
				continue;
			}

			log("\nNext accepted favorite axiom: " + favorite);
			// discard axiom favorite from the agenda
			currentAgenda.remove(favorite);

			Set<OWLAxiom> currentAxioms = result.axioms().collect(Collectors.toSet());
			currentAxioms.add(favorite);
			while (!Utils.isConsistent(currentAxioms)) {
				log("\n** Weakening. **");
				currentAxioms.remove(favorite);
				// weakening of favorite axiom
				AxiomWeakener axiomWeakener = new AxiomWeakener(referenceOntology);

				Set<OWLAxiom> weakerAxioms = axiomWeakener.getWeakerAxioms(favorite);

				int randomPick = ThreadLocalRandom.current().nextInt(0, weakerAxioms.size());
				favorite = (OWLAxiom) (weakerAxioms.toArray())[randomPick];
				currentAxioms.add(favorite);
			}
			log("\nAdding axiom: " + favorite);
			result.add(favorite);

			// next turn
			currentVoter = (currentVoter + 1) % numVoters;
		}

		if (currentAgenda.isEmpty()) {
			log("\n-- End of procedure: all axioms of the agenda have been considered.\n");
		}
		if (haveGivenUp.size() >= numVoters) {
			log("\n-- End of procedure: all voters have given up.\n");
		}

		return result;
	}

}
