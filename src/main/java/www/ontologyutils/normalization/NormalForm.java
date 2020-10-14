package www.ontologyutils.normalization;

import java.util.Set;

import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;

import uk.ac.manchester.cs.owl.owlapi.OWLQuantifiedRestrictionImpl;

/**
 * @author nico
 *
 *
 *         A TBox axiom in normal form can be of one of four types:
 *         <ul>
 *         <li>Type 1: Subclass(atom or conjunction of atoms, atom or
 *         disjunction of atoms)
 *         <li>Type 2: Subclass(atom, exists property atom)
 *         <li>Type 3: Subclass(atom, forall property atom)
 *         <li>Type 4: Subclass(exists property atom, atom)
 *         </ul>
 * 
 *         TODO: This is an early prototype and the definitions may change.
 */
public class NormalForm {

	public static boolean isNormalFormTBoxAxiom(OWLAxiom ax) {
		if (!ax.isOfType(AxiomType.SUBCLASS_OF)) {
			return false;
		}

		OWLClassExpression left = ((OWLSubClassOfAxiom) ax).getSubClass();
		OWLClassExpression right = ((OWLSubClassOfAxiom) ax).getSuperClass();

		if (typeOneSubClassAxiom(left, right) || typeTwoSubClassAxiom(left, right)
				|| typeThreeSubClassAxiom(left, right) || typeFourSubClassAxiom(left, right)) {
			return true;
		}

		return false;
	}

	public static boolean typeOneSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return ((isAtom(left) || isConjunctionOfAtoms(left)) && (isAtom(right) || isDisjunctionOfAtoms(right)));
	}

	public static boolean typeTwoSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isExistentialOfAtom(right));
	}

	public static boolean typeThreeSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isUniversalOfAtom(right));
	}

	public static boolean typeFourSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isExistentialOfAtom(left) && isAtom(right));
	}

	public static boolean isAtom(OWLClassExpression e) {
		return e.isOWLClass() || e.isTopEntity() || e.isBottomEntity();
	}

	public static boolean isTypeAAtom(OWLClassExpression e) {
		return e.isOWLClass() || e.isTopEntity();
	}

	public static boolean isTypeBAtom(OWLClassExpression e) {
		return e.isOWLClass() || e.isBottomEntity();
	}

	public static boolean isConjunctionOfAtoms(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_INTERSECTION_OF)) {
			return false;
		}
		Set<OWLClassExpression> conjunctions = e.asConjunctSet();
		for (OWLClassExpression c : conjunctions) {
			if (!isAtom(c)) {
				return false;
			}
		}
		return true;
	}

	public static boolean isDisjunctionOfAtoms(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_UNION_OF)) {
			return false;
		}
		Set<OWLClassExpression> disjunctions = e.asDisjunctSet();
		for (OWLClassExpression d : disjunctions) {
			if (!isAtom(d)) {
				return false;
			}
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	public static boolean isExistentialOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_SOME_VALUES_FROM)) {
			return false;
		}

		OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) e).getFiller();

		if (!isAtom(filler)) {
			return false;
		}
		return true;
	}

	@SuppressWarnings("unchecked")
	public static boolean isUniversalOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_ALL_VALUES_FROM)) {
			return false;
		}

		OWLClassExpression filler = ((OWLQuantifiedRestrictionImpl<OWLClassExpression>) e).getFiller();

		if (!isAtom(filler)) {
			return false;
		}
		return true;
	}

}
