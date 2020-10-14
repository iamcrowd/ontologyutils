package www.ontologyutils.normalization;

import java.security.InvalidParameterException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;


import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLAnnotation;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalDataPropertyAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiomShortCut;

import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLDisjointClassesAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLDisjointUnionAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLEquivalentClassesAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectAllValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectIntersectionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectPropertyDomainAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectPropertyRangeAxiomImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectSomeValuesFromImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLObjectUnionOfImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLQuantifiedRestrictionImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLSubClassOfAxiomImpl;

import www.ontologyutils.toolbox.AnnotateOrigin;
import www.ontologyutils.toolbox.FreshAtoms;

public class NormalizationTools {

	private static final Collection<OWLAnnotation> EMPTY_ANNOTATION = new ArrayList<OWLAnnotation>();

	private static final OWLClassExpression TOP = new OWLDataFactoryImpl().getOWLThing();
	private static final OWLClassExpression BOT = new OWLDataFactoryImpl().getOWLNothing();

	/**
	 * @param ax
	 * @return a collection of subclass axioms that are equivalent to ax
	 * 
	 *         This is a function that completes {@code asSubClassOfAxioms} that
	 *         already exists for {@code OWLEquivalentClassesAxiomImpl} and
	 *         {@code OWLDisjointClassesAxiomImpl} and for
	 *         {@code OWLSubClassOfAxiomShortCut} in general. It thus obviously
	 *         works for axiom types subclass, equivalent class, disjoint class.
	 *         Moreover, we extend it to axiom types: disjoint union, object
	 *         property range, object property domain.
	 */
	public static Collection<OWLSubClassOfAxiom> asSubClassOfAxioms(OWLAxiom ax) throws InvalidParameterException {
		Collection<OWLSubClassOfAxiom> subClassOfAxioms = new ArrayList<OWLSubClassOfAxiom>();

		// If ax is a subclass axiom, there is nothing to do.
		if (ax.isOfType(AxiomType.SUBCLASS_OF)) {
			subClassOfAxioms.add((OWLSubClassOfAxiom) ax);
		}
		// If ax is an equivalent class axiom, we can use asOWLSubClassOfAxioms().
		else if (ax.isOfType(AxiomType.EQUIVALENT_CLASSES)) {
			subClassOfAxioms = ((OWLEquivalentClassesAxiomImpl) ax).asOWLSubClassOfAxioms();
		}
		// If ax is a disjoint class axiom, we can use asOWLSubClassOfAxioms().
		else if (ax.isOfType(AxiomType.DISJOINT_CLASSES)) {
			subClassOfAxioms = ((OWLDisjointClassesAxiomImpl) ax).asOWLSubClassOfAxioms();
		}
		// If ax is a disjoint union axiom, we must first transform them into one
		// disjoint class axiom
		// and one equivalent class axiom. Then, we can use asOWLSubClassOfAxioms().
		else if (ax.isOfType(AxiomType.DISJOINT_UNION)) {
			OWLDisjointClassesAxiom disjointClasses = ((OWLDisjointUnionAxiomImpl) ax).getOWLDisjointClassesAxiom();
			OWLEquivalentClassesAxiom equivalentClasses = ((OWLDisjointUnionAxiomImpl) ax)
					.getOWLEquivalentClassesAxiom();
			subClassOfAxioms = disjointClasses.asOWLSubClassOfAxioms();
			subClassOfAxioms.addAll(equivalentClasses.asOWLSubClassOfAxioms());
		}
		// If ax is an object property axiom, we can use
		// property R with range C ==> subclass(top, forall R. C)
		else if (ax.isOfType(AxiomType.OBJECT_PROPERTY_RANGE)) {
			OWLObjectPropertyExpression property = ((OWLObjectPropertyRangeAxiomImpl) ax).getProperty();
			OWLClassExpression range = ((OWLObjectPropertyRangeAxiomImpl) ax).getRange();
			OWLSubClassOfAxiom scoa = new OWLSubClassOfAxiomImpl(TOP, new OWLObjectAllValuesFromImpl(property, range),
					EMPTY_ANNOTATION);
			subClassOfAxioms.add(scoa);
		}
		// If ax is an object domain axiom, we can use
		// property R with domain C ==> subclass(exists R. top, C)
		else if (ax.isOfType(AxiomType.OBJECT_PROPERTY_DOMAIN)) {
			OWLObjectPropertyExpression property = ((OWLObjectPropertyDomainAxiomImpl) ax).getProperty();
			OWLClassExpression domain = ((OWLObjectPropertyDomainAxiomImpl) ax).getDomain();
			OWLSubClassOfAxiom scoa = new OWLSubClassOfAxiomImpl(new OWLObjectSomeValuesFromImpl(property, TOP), domain,
					EMPTY_ANNOTATION);
			subClassOfAxioms.add(scoa);
		} else if (ax.isOfType(AxiomType.FUNCTIONAL_OBJECT_PROPERTY)) {
			subClassOfAxioms = Collections.singleton(((OWLFunctionalObjectPropertyAxiom) ax).asOWLSubClassOfAxiom());
		} else if (ax.isOfType(AxiomType.DATA_PROPERTY_RANGE)) {
			subClassOfAxioms = Collections.singleton(((OWLDataPropertyRangeAxiom) ax).asOWLSubClassOfAxiom());
		} else if (ax.isOfType(AxiomType.DATA_PROPERTY_DOMAIN)) {
			subClassOfAxioms = Collections.singleton(((OWLSubClassOfAxiomShortCut) ax).asOWLSubClassOfAxiom());
		} else if (ax.isOfType(AxiomType.FUNCTIONAL_DATA_PROPERTY)) {
			subClassOfAxioms = Collections.singleton(((OWLFunctionalDataPropertyAxiom) ax).asOWLSubClassOfAxiom());
		} 	
		else {
			throw new RuntimeException("The axiom " + ax + " of type " + ax.getAxiomType()
					+ " could not be converted into subclass axioms.");
		}
		
		// we add an annotation to each axiom referring to the original axiom in parameter
		Collection<OWLSubClassOfAxiom> annotatedSubClassOfAxioms = new ArrayList<OWLSubClassOfAxiom>();
		subClassOfAxioms.forEach(a -> 
			annotatedSubClassOfAxioms.add((OWLSubClassOfAxiom) AnnotateOrigin.getAnnotatedAxiom(a,ax)));
		
		return annotatedSubClassOfAxioms;
	}

	/**
	 * @param ax
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static Collection<OWLSubClassOfAxiom> normalizeSubClassAxiom(OWLSubClassOfAxiom ax) {
		Collection<OWLSubClassOfAxiom> normalizedAxioms = new ArrayList<OWLSubClassOfAxiom>();
		LinkedList<OWLSubClassOfAxiom> axioms = new LinkedList<OWLSubClassOfAxiom>();
		axioms.add(ax);

		while (!axioms.isEmpty()) {

			OWLSubClassOfAxiom currentAxiom = axioms.remove();
			if (NormalForm.isNormalFormTBoxAxiom(currentAxiom)) {
				normalizedAxioms.add(currentAxiom);
				continue;
			}
			// if currentAxiom is not in normal form
			OWLClassExpression left = currentAxiom.getSubClass();
			OWLClassExpression right = currentAxiom.getSuperClass();

			// If left is disjunction or right is conjunction,
			// simple transformations can be done without introducing fresh variables.
			// We deal with these two cases in priority.

			// left is disjunction
			if (left.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
				Set<OWLClassExpression> disjunctions = left.asDisjunctSet();
				for (OWLClassExpression d : disjunctions) {
					OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(d, right, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
					axioms.add(sba);
				}
			}
			// right is conjunction
			else if (right.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				Set<OWLClassExpression> conjunctions = right.asConjunctSet();
				for (OWLClassExpression c : conjunctions) {
					OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(left, c, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
					axioms.add(sba);
				}
			}

			// If right is disjunction or left is conjunction

			// left is conjunction
			else if (left.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF) {
				if (!NormalForm.isConjunctionOfAtoms(left)) {
					Set<OWLClassExpression> conjuncts = left.asConjunctSet();
					Set<OWLClassExpression> newConjuncts = new HashSet<>();

					for (OWLClassExpression conj : conjuncts) {
						if (NormalForm.isAtom(conj)) {
							newConjuncts.add(conj);
						} else {
							// creating fresh concept
							OWLClassExpression fresh = FreshAtoms.createFreshAtomCopy(conj);
							// it'll be a new atomic conjunct
							newConjuncts.add(fresh);

							// adding fresh -> conj
							OWLSubClassOfAxiom sbaFreshOce = new OWLSubClassOfAxiomImpl(fresh, conj, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
							axioms.add(sbaFreshOce);
							// adding conj -> fresh
							OWLSubClassOfAxiom sbaOceFresh = new OWLSubClassOfAxiomImpl(conj, fresh, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
							axioms.add(sbaOceFresh);

						}
					}
					// adding new_conjunction -> right
					OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(
							new OWLObjectIntersectionOfImpl(newConjuncts.stream()), right, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
					axioms.add(sba);
				}

			}
			// right is disjunction
			else if (right.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF) {
				if (!NormalForm.isDisjunctionOfAtoms(right)) {
					Set<OWLClassExpression> disjuncts = right.asDisjunctSet();
					Set<OWLClassExpression> newDisjuncts = new HashSet<>();

					for (OWLClassExpression disj : disjuncts) {
						if (NormalForm.isAtom(disj)) {
							newDisjuncts.add(disj);
						} else {
							// creating fresh concept
							OWLClassExpression fresh = FreshAtoms.createFreshAtomCopy(disj);
							// it'll be a new atomic disjunct
							newDisjuncts.add(fresh);

							// adding fresh -> disj
							OWLSubClassOfAxiom sbaFreshOce = new OWLSubClassOfAxiomImpl(fresh, disj, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
							axioms.add(sbaFreshOce);
							// adding disj -> fresh
							OWLSubClassOfAxiom sbaOceFresh = new OWLSubClassOfAxiomImpl(disj, fresh, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
							axioms.add(sbaOceFresh);

						}
					}
					// adding left -> new_disjunction
					OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(left,
							new OWLObjectUnionOfImpl(newDisjuncts.stream()), AnnotateOrigin.getAxiomAnnotations(currentAxiom));
					axioms.add(sba);
				}
			}

			// If left or right is negation

			// left is negation
			else if (left.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF) {
				// left = not filler
				OWLClassExpression filler = ((OWLObjectComplementOf) left).getOperand(); // left.getComplementNNF();

				// we add : top -> filler or right
				Set<OWLClassExpression> operands = right.asDisjunctSet();
				operands.add(filler);
				OWLObjectUnionOfImpl newRight = new OWLObjectUnionOfImpl(operands.stream());

				OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(TOP, newRight, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sba);
			}
			// right is negation
			else if (right.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF) {
				// right = not filler
				OWLClassExpression filler = ((OWLObjectComplementOf) right).getOperand(); // right.getComplementNNF();

				// we add : left and filler -> bot
				Set<OWLClassExpression> operands = left.asConjunctSet();
				operands.add(filler);
				OWLObjectIntersectionOfImpl newLeft = new OWLObjectIntersectionOfImpl(operands.stream());

				OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(newLeft, BOT, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sba);
			}

			// If left or right is existential

			else if ((left.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)
					&& !NormalForm.isExistentialOfAtom(left)) { // left existential atom is fine
				// left = exists property filler
				OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) left).getFiller();
				OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom) left).getProperty();

				// creating fresh concept
				OWLClassExpression fresh = FreshAtoms.createFreshAtomCopy(filler);

				// we add exists property fresh -> right
				OWLObjectSomeValuesFromImpl evf = new OWLObjectSomeValuesFromImpl(property, fresh);
				OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(evf, right, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sba);

				// we add fresh -> filler
				OWLSubClassOfAxiom sbaFreshFiller = new OWLSubClassOfAxiomImpl(fresh, filler, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sbaFreshFiller);

				// we add filler -> fresh
				OWLSubClassOfAxiom sbaFillerFresh = new OWLSubClassOfAxiomImpl(filler, fresh, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sbaFillerFresh);
			} else if ((right.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)
					&& !NormalForm.isExistentialOfAtom(right)) { // right existential atom is fine
				// right = exists property filler
				OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) right).getFiller();
				OWLObjectPropertyExpression property = ((OWLObjectSomeValuesFrom) right).getProperty();

				// creating fresh concept
				OWLClassExpression fresh = FreshAtoms.createFreshAtomCopy(filler);

				// we add left -> exists property fresh
				OWLObjectSomeValuesFromImpl evf = new OWLObjectSomeValuesFromImpl(property, fresh);
				OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(left, evf, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sba);

				// we add fresh -> filler
				OWLSubClassOfAxiom sbaFreshFiller = new OWLSubClassOfAxiomImpl(fresh, filler, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sbaFreshFiller);

				// we add filler -> fresh
				OWLSubClassOfAxiom sbaFillerFresh = new OWLSubClassOfAxiomImpl(filler, fresh, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sbaFillerFresh);
			}

			// If left or right is universal

			else if ((left.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)) {
				// we just take the contrapositive
				OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(right.getComplementNNF(), left.getComplementNNF(),
						AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sba);
			} else if ((right.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)
					&& !NormalForm.isUniversalOfAtom(right)) { // right universal atom is fine
				// right = forall property filler
				OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) right).getFiller();
				OWLObjectPropertyExpression property = ((OWLObjectAllValuesFrom) right).getProperty();

				// creating fresh concept
				OWLClassExpression fresh = FreshAtoms.createFreshAtomCopy(filler);

				// we add left -> forall property fresh
				OWLObjectAllValuesFromImpl avf = new OWLObjectAllValuesFromImpl(property, fresh);
				OWLSubClassOfAxiom sba = new OWLSubClassOfAxiomImpl(left, avf, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sba);

				// we add fresh -> filler
				OWLSubClassOfAxiom sbaFreshFiller = new OWLSubClassOfAxiomImpl(fresh, filler, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sbaFreshFiller);

				// we add filler -> fresh
				OWLSubClassOfAxiom sbaFillerFresh = new OWLSubClassOfAxiomImpl(filler, fresh, AnnotateOrigin.getAxiomAnnotations(currentAxiom));
				axioms.add(sbaFillerFresh);
			} else {
				throw new RuntimeException("I don't know what to do with " + ax);
			}

		} // end while

		return normalizedAxioms;
	}

}
