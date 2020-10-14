package www.ontologyutils.normalization;

import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.parameters.Imports; 

import uk.ac.manchester.cs.owl.owlapi.OWLObjectAllValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectComplementOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLQuantifiedRestrictionImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLSubClassOfAxiomImpl;

import www.ontologyutils.toolbox.AnnotateOrigin;
import www.ontologyutils.toolbox.FreshAtoms;
import www.ontologyutils.toolbox.Utils;

/**
 * TODO: reorganize code into interface + implementations
 */
public class Normalization {

	private static final Collection<OWLAnnotation> EMPTY_ANNOTATION = new ArrayList<OWLAnnotation>();

	/**
	 * @param ontology
	 *            with TBox axioms all in subclass form.
	 * @see {@code asSubClassOfAxioms}
	 * @return A normalized version of {@code ontology}.
	 * @throws OWLOntologyCreationException
	 */
	public static OWLOntology normalizeNaive(OWLOntology ontology) {
		// we make a copy of the ontology without the TBox
		OWLOntology newOntology = Utils.newEmptyOntology();
		newOntology.addAxioms(ontology.rboxAxioms(Imports.EXCLUDED));
		newOntology.addAxioms(ontology.aboxAxioms(Imports.EXCLUDED));

		Set<OWLAxiom> tBoxAxioms = ontology.tboxAxioms(Imports.EXCLUDED).collect(Collectors.toSet());

		tBoxAxioms.forEach(
				ax -> newOntology.addAxioms(NormalizationTools.normalizeSubClassAxiom((OWLSubClassOfAxiom) ax)));

		return newOntology;
	}

	/**
	 * @param ontology
	 *            with TBox axioms all in subclass form.
	 * @see {@code asSubClassOfAxioms}
	 * @return A normalized version of {@code ontology}, following the procedure of
	 *         Simancik et al. "Consequence-Based Reasoning beyond Horn Ontologies"
	 *         (IJCAI 2011).
	 * @throws OWLOntologyCreationException
	 */
	public static OWLOntology normalizeCondor(OWLOntology ontology) {

		// we make a copy of the ontology without the TBox
		OWLOntology newOntology = Utils.newEmptyOntology();
		newOntology.addAxioms(ontology.rboxAxioms(Imports.EXCLUDED));
		newOntology.addAxioms(ontology.aboxAxioms(Imports.EXCLUDED));

		Set<OWLAxiom> tBoxAxioms = ontology.tboxAxioms(Imports.EXCLUDED).collect(Collectors.toSet());

		// we replace negative occurrences of forall p C with not exists p not C
		Set<OWLClassExpression> subConcepts = Utils.getSubOfTBox(ontology);
		for (OWLClassExpression e : subConcepts) {
			Set<OWLAxiom> newtBoxAxioms = new HashSet<OWLAxiom>(tBoxAxioms);
			if (e.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM) {
				newtBoxAxioms.stream().forEach(a -> {
					tBoxAxioms.remove(a);
					tBoxAxioms.add(substituteNegativeForAll((OWLObjectAllValuesFrom) e, (OWLSubClassOfAxiom) a));
				});
			}
		}
		newOntology.addAxioms(tBoxAxioms);

		// we get the structural transformation of newOntology
		OWLOntology transformed = structuralTransformation(newOntology);

		// replace X -> Y and Z with two axioms X -> Y and X -> Z
		// replace X or Y -> Z with two axioms X -> Z and Y -> Z
		// replace X -> not Y with X and Y -> bot
		// replace not X -> Y with top -> X or Y
		transformed.tboxAxioms(Imports.EXCLUDED).forEach(axiom -> {
			transformed.removeAxiom(axiom);
			transformed.addAxioms(NormalizationTools.normalizeSubClassAxiom((OWLSubClassOfAxiom) axiom));
		});

		return transformed;
	}

	private static OWLAxiom substituteNegativeForAll(OWLObjectAllValuesFrom e, OWLSubClassOfAxiom a) {
		OWLObjectPropertyExpression property = e.getProperty();
		OWLClassExpression filler = e.getFiller();

		// new concept: not exists property not filler
		OWLObjectComplementOf substitute = new OWLObjectComplementOfImpl(
				new OWLObjectSomeValuesFromImpl(property, new OWLObjectComplementOfImpl(filler)));

		OWLClassExpression newLeft = replaceIfPolarity(e, substitute, a.getSubClass(), true);
		OWLClassExpression newRight = replaceIfPolarity(e, substitute, a.getSuperClass(), false);

		return new OWLSubClassOfAxiomImpl(newLeft, newRight, AnnotateOrigin.getAxiomAnnotations(a));
	}

	/**
	 * @param e
	 *            a forall expression
	 * @param substitute
	 *            a substitute not exists no expression for {@code e}
	 * @param in
	 *            the expression in which to substitute {@code e} with
	 *            {@code substitute}
	 * @param polarity
	 *            substitute {@code e} with {@code substitute} when {@code e}
	 *            appears positively ({@code polarity} is true) or negatively
	 *            ({@code polarity} is false) in {@code in}
	 * @return the resulting expression
	 */
	private static OWLClassExpression replaceIfPolarity(OWLObjectAllValuesFrom e, OWLObjectComplementOf substitute,
			OWLClassExpression in, Boolean polarity) {
		/*
		 * if (polarity ? !isPositiveIn(e, in) : !isNegativeIn(e, in)) { return in; }
		 */

		switch (in.getClassExpressionType()) {
		case OWL_CLASS: {
			return in;
		}
		case OBJECT_COMPLEMENT_OF: {
			OWLClassExpression op = ((OWLObjectComplementOf) in).getOperand();
			return new OWLObjectComplementOfImpl(replaceIfPolarity(e, substitute, op, !polarity));
		}
		case OBJECT_UNION_OF: {
			Set<OWLClassExpression> disjuncts = in.asDisjunctSet();
			return new OWLObjectUnionOfImpl(disjuncts.stream().map(d -> replaceIfPolarity(e, substitute, d, polarity)));
		}
		case OBJECT_INTERSECTION_OF: {
			Set<OWLClassExpression> conjuncts = in.asConjunctSet();
			return new OWLObjectIntersectionOfImpl(
					conjuncts.stream().map(c -> replaceIfPolarity(e, substitute, c, polarity)));
		}
		case OBJECT_SOME_VALUES_FROM: {
			OWLClassExpression filler = ((OWLObjectSomeValuesFrom) in).getFiller();
			OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom) in).getProperty();
			return new OWLObjectSomeValuesFromImpl(property, replaceIfPolarity(e, substitute, filler, polarity));
		}
		case OBJECT_ALL_VALUES_FROM: {
			if (Utils.sameConcept(e, in)) {
				return polarity ? substitute : e;
			}
			OWLClassExpression filler = ((OWLObjectAllValuesFrom) in).getFiller();
			OWLObjectPropertyExpression property = ((OWLObjectAllValuesFrom) in).getProperty();
			return new OWLObjectAllValuesFromImpl(property, replaceIfPolarity(e, substitute, filler, polarity));

		}
		default:
			throw new RuntimeException();
		}
	}

	/**
	 * @param ontology
	 *            with TBox axioms all in subclass form.
	 * @see {@code asSubClassOfAxioms}
	 * @return A new ontology with the TBox axioms structurally transformed,
	 *         following the procedure of Simancik et al. "Consequence-Based
	 *         Reasoning beyond Horn Ontologies" (IJCAI 2011).
	 */
	private static OWLOntology structuralTransformation(OWLOntology ontology) {

		OWLOntology newOntology = Utils.newEmptyOntology();
		newOntology.addAxioms(ontology.rboxAxioms(Imports.EXCLUDED));
		newOntology.addAxioms(ontology.aboxAxioms(Imports.EXCLUDED));

		Collection<OWLSubClassOfAxiom> transformed = new ArrayList<>();
		Set<OWLClassExpression> subConcepts = Utils.getSubOfTBox(ontology);
		Map<OWLClassExpression, OWLClassExpression> map = new HashMap<>();

		for (OWLClassExpression e : subConcepts) {
			if (e.isOWLClass()) {
				map.put(e, e);
			} else { // as per the article it should be like that always
				OWLClassExpression fresh = FreshAtoms.createFreshAtomCopy(e);
				map.put(e, fresh);
			}
		}

		for (OWLClassExpression e : subConcepts) {
			if (e.isOWLClass()) { // as per the article it shouldn't be skipped
				continue;
			}
			if (ontology.tboxAxioms(Imports.EXCLUDED).anyMatch(ax -> isNegativeIn(e, ax))) {
				ontology.tboxAxioms(Imports.EXCLUDED).forEach(ax -> {
					if (isNegativeIn(e, ax)) {
						OWLSubClassOfAxiomImpl sba = new OWLSubClassOfAxiomImpl(structuralTransformation(e, map),
								map.get(e), AnnotateOrigin.getAxiomAnnotations(ax));
						transformed.add(sba);
					}
				});
			}
			if (ontology.tboxAxioms(Imports.EXCLUDED).anyMatch(ax -> isPositiveIn(e, ax))) {
				ontology.tboxAxioms(Imports.EXCLUDED).forEach(ax -> {
					if (isPositiveIn(e, ax)) {
						OWLSubClassOfAxiomImpl sba = new OWLSubClassOfAxiomImpl(map.get(e),
								structuralTransformation(e, map), AnnotateOrigin.getAxiomAnnotations(ax));
						transformed.add(sba);
					}
				});
			}
		}

		ontology.tboxAxioms(Imports.EXCLUDED).forEach((a) -> {
			if (!(a instanceof OWLSubClassOfAxiom)) {
				throw new RuntimeException("Axiom " + a + " should be a subclass axiom.");
			} else {
				OWLClassExpression left = ((OWLSubClassOfAxiom) a).getSubClass();
				OWLClassExpression right = ((OWLSubClassOfAxiom) a).getSuperClass();

				OWLSubClassOfAxiomImpl sba = new OWLSubClassOfAxiomImpl(map.get(left), map.get(right),
						AnnotateOrigin.getAxiomAnnotations(a));
				transformed.add(sba);
			}
		});

		newOntology.addAxioms(transformed);

		return newOntology;
	}

	@SuppressWarnings("unchecked")
	private static boolean isPositiveIn(OWLClassExpression e, OWLClassExpression in) {
		if (e.equals(in)) {
			return true;
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF)) {
			return in.asDisjunctSet().stream().anyMatch(disj -> isPositiveIn(e, (OWLClassExpression) disj));
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF)) {
			return in.asConjunctSet().stream().anyMatch(conj -> isPositiveIn(e, (OWLClassExpression) conj));
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)) {
			return isPositiveIn(e, ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) in).getFiller());
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)) {
			return isPositiveIn(e, ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) in).getFiller());
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF)) {
			return isNegativeIn(e, ((OWLObjectComplementOf) in).getOperand());
		}

		return false;
	}

	private static boolean isPositiveIn(OWLClassExpression e, OWLAxiom ax) {
		OWLClassExpression left = ((OWLSubClassOfAxiom) ax).getSubClass();
		OWLClassExpression right = ((OWLSubClassOfAxiom) ax).getSuperClass();

		return isPositiveIn(e, right) || isNegativeIn(e, left);
	}

	@SuppressWarnings("unchecked")
	private static boolean isNegativeIn(OWLClassExpression e, OWLClassExpression in) {
		if (e.equals(in)) {
			return false;
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF)) {
			return in.asDisjunctSet().stream().anyMatch(disj -> isNegativeIn(e, (OWLClassExpression) disj));
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF)) {
			return in.asConjunctSet().stream().anyMatch(conj -> isNegativeIn(e, (OWLClassExpression) conj));
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)) {
			return isNegativeIn(e, ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) in).getFiller());
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)) {
			return isNegativeIn(e, ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) in).getFiller());
		} else if ((in.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF)) {
			return isPositiveIn(e, ((OWLObjectComplementOf) in).getOperand());
		}

		return false;
	}

	private static boolean isNegativeIn(OWLClassExpression e, OWLAxiom ax) {
		OWLClassExpression left = ((OWLSubClassOfAxiom) ax).getSubClass();
		OWLClassExpression right = ((OWLSubClassOfAxiom) ax).getSuperClass();

		return isPositiveIn(e, left) || isNegativeIn(e, right);
	}

	@SuppressWarnings("unchecked")
	private static OWLClassExpression structuralTransformation(OWLClassExpression e,
			Map<OWLClassExpression, OWLClassExpression> map) {

		if (e.isTopEntity()) {
			return e;
		} else if (e.isBottomEntity()) {
			return e;
		} else if (e.isOWLClass()) {
			return e;
		} else if (e instanceof OWLObjectComplementOf) {
			return new OWLObjectComplementOfImpl(map.get(((OWLObjectComplementOf) e).getOperand()));
		} else if ((e.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF)) {
			Set<OWLClassExpression> conjunctions = e.asConjunctSet();
			return new OWLObjectIntersectionOfImpl(conjunctions.stream().map((c) -> map.get(c)));
		} else if ((e.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF)) {
			Set<OWLClassExpression> disjunctions = e.asDisjunctSet();
			return new OWLObjectUnionOfImpl(disjunctions.stream().map((c) -> map.get(c)));
		} else if ((e.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)) {
			OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) e).getFiller();
			OWLObjectPropertyExpression property = ((OWLObjectAllValuesFrom) e).getProperty();
			return new OWLObjectAllValuesFromImpl(property, map.get(filler));
		} else if ((e.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)) {
			OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) e).getFiller();
			OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom) e).getProperty();
			return new OWLObjectSomeValuesFromImpl(property, map.get(filler));
		} else {
			throw new InvalidParameterException("The expression " + e + " can not be transformed.");
		}
	}

}
