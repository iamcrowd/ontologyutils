package www.ontologyutils.normalization;

import java.util.Set;

import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.ClassExpressionType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;

import uk.ac.manchester.cs.owl.owlapi.OWLDataMaxCardinalityImpl;

import uk.ac.manchester.cs.owl.owlapi.OWLQuantifiedRestrictionImpl;
import uk.ac.manchester.cs.owl.owlapi.OWLCardinalityRestrictionImpl;

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

		if (typeOneSubClassAxiom(left, right) 	||
				
			typeTwoSubClassAxiom(left, right) 	||
			typeTwoMinCardAxiom(left, right) ||
			typeTwoMaxCardAxiom(left, right) ||
			typeTwoExactCardAxiom(left, right) ||
			
			typeTwoDataSubClassAxiom(left, right) ||
			typeTwoDataMinCardAxiom(left, right) ||
			typeTwoDataMaxCardAxiom(left, right) ||
			typeTwoDataExactCardAxiom(left, right) ||
			
			typeThreeSubClassAxiom(left, right) || 
			typeThreeDataSubClassAxiom(left, right) ||
			
			typeFourSubClassAxiom(left, right) 	||
			typeFourDataSubClassAxiom(left, right)
			) {
			return true;
		}

		return false;
	}

	public static boolean typeOneSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return ((isAtom(left) || isConjunctionOfAtoms(left)) && (isAtom(right) || isDisjunctionOfAtoms(right)));
	}

	/**
	 * Check (atom, negation atom) CIs
	 * 
	 * @param left an OWLClassExpression
	 * @param right an OWLClassExpression
	 * @return
	 */
	public static boolean complementExpression(OWLClassExpression left, OWLClassExpression right) {
		return ((isAtom(left) && isComplementOfAtoms(right)));
	}

	/**
	 * Subclass(atom, exists property atom)
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	public static boolean typeTwoSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isExistentialOfAtom(right));
	}
	
	/**
	 * Subclass(atom, exists dataproperty atom)
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	public static boolean typeTwoDataSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isExistentialOfData(right));
	}
	
	/**
	 * subclass(atom, mincardinality property atom)
	 */
	public static boolean typeTwoMinCardAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isMinCardinalityOfAtom(right));
	}
	
	/**
	 * subclass(atom, maxcardinality property atom)
	 */
	public static boolean typeTwoMaxCardAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isMaxCardinalityOfAtom(right));
	}

	/**
	 * subclass(atom, exactcardinality property atom)
	 */
	public static boolean typeTwoExactCardAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isExactCardinalityOfAtom(right));
	}
	
	/**
	 * subclass(atom, mincardinality dataproperty atom)
	 */
	public static boolean typeTwoDataMinCardAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isDataMinCardinalityOfAtom(right));
	}
	
	/**
	 * subclass(atom, maxcardinality dataproperty atom)
	 */
	public static boolean typeTwoDataMaxCardAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isDataMaxCardinalityOfAtom(right));
	}
	
	/**
	 * subclass(atom, exactcardinality dataproperty atom)
	 */
	public static boolean typeTwoDataExactCardAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isDataExactCardinalityOfAtom(right));
	}

	/**
	 * subclass(atom, forall property atom)
	 * @param left
	 * @param right
	 * @return
	 */
	public static boolean typeThreeSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isUniversalOfAtom(right));
	}
	
	/**
	 * subclass(atom, forall dataproperty atom)
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	public static boolean typeThreeDataSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isAtom(left) && isUniversalOfData(right));
	}

	/**
	 * sublcass(exists property atom, atom)
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	public static boolean typeFourSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isExistentialOfAtom(left) && isAtom(right));
	}

	/**
	 * sublcass(exists dataproperty atom, atom)
	 * 
	 * @param left
	 * @param right
	 * @return
	 */
	public static boolean typeFourDataSubClassAxiom(OWLClassExpression left, OWLClassExpression right) {
		return (isExistentialOfData(left) && isAtom(right));
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

	/**
	 * Check if e is an object complement expression
	 * 
	 * @param e
	 * @return
	 */
	public static boolean isComplementOfAtoms(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_COMPLEMENT_OF)) {
			return false;
		}
		
		OWLClassExpression complement = ((OWLObjectComplementOf) e).getOperand();

		if (isAtom(complement)) {
				return true;
		}
		return false;
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
	
	/**
	 * Data Some Values From expression
	 * 
	 * @param e
	 * @return
	 * @implNote This function does not consider composed fillers. They can be only Datatypes
	 */
	@SuppressWarnings("unchecked")
	public static boolean isExistentialOfData(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.DATA_SOME_VALUES_FROM)) {
			return false;
		}
		
		OWLDataRange filler = ((OWLQuantifiedRestrictionImpl<OWLDataRange>) e).getFiller();

		if (!filler.isOWLDatatype()) {
			return false;
		}
		return true;
	}
	

	/**
	 * Object Min Cardinality Expression
	 * 
	 * @param e
	 * @return
	 * @implNote This function does not consider composed fillers. They can be only Datatypes
	 */
	public static boolean isMinCardinalityOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_MIN_CARDINALITY)) {
			return false;
		}

		@SuppressWarnings("unchecked")
		OWLClassExpression filler = ((OWLCardinalityRestrictionImpl<OWLClassExpression>) e).getFiller();

		if (!isAtom(filler)) {
			return false;
		}
		return true;
	}
	
	/**
	 * Object Max Cardinality Expression
	 * 
	 * @param e
	 * @return
	 * 
	 */
	@SuppressWarnings("unchecked")
	public static boolean isMaxCardinalityOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_MAX_CARDINALITY)) {
			return false;
		}

		OWLClassExpression filler = ((OWLCardinalityRestrictionImpl<OWLClassExpression>) e).getFiller();

		if (!isAtom(filler)) {
			return false;
		}
		return true;
	}
	
	/**
	 * Object Exact Cardinality Expression
	 * 
	 * @param e
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static boolean isExactCardinalityOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.OBJECT_EXACT_CARDINALITY)) {
			return false;
		}

		OWLClassExpression filler = ((OWLCardinalityRestrictionImpl<OWLClassExpression>) e).getFiller();

		if (!isAtom(filler)) {
			return false;
		}
		return true;
	}
	
	/**
	 * Data Min Cardinality Expression
	 * 
	 * @param e
	 * @return
	 * @implNote This function does not consider composed fillers. They can be only Datatypes
	 */
	@SuppressWarnings("unchecked")
	public static boolean isDataMinCardinalityOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.DATA_MIN_CARDINALITY)) {
			return false;
		}

		OWLDataRange filler = ((OWLCardinalityRestrictionImpl<OWLDataRange>) e).getFiller();

		if (!filler.isOWLDatatype()) {
			return false;
		}
		return true;
	}
	
	/**
	 * Data Max Cardinality Expression
	 * 
	 * @param e
	 * @return
	 * @implNote This function does not consider composed fillers. They can be only Datatypes
	 */
	@SuppressWarnings("unchecked")
	public static boolean isDataMaxCardinalityOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.DATA_MAX_CARDINALITY)) {
			return false;
		}
		
		OWLDataRange filler = ((OWLCardinalityRestrictionImpl<OWLDataRange>) e).getFiller();

		if (!filler.isOWLDatatype()) {
			return false;
		}
		return true;
	}
	
	/**
	 * Data Exact Cardinality Expression
	 * 
	 * @param e
	 * @return
	 * @implNote This function does not consider composed fillers. They can be only Datatypes
	 */
	@SuppressWarnings("unchecked")
	public static boolean isDataExactCardinalityOfAtom(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.DATA_EXACT_CARDINALITY)) {
			return false;
		}

		OWLDataRange filler = ((OWLCardinalityRestrictionImpl<OWLDataRange>) e).getFiller();

		if (!filler.isOWLDatatype()) {
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
	
	/**
	 * Data All Values From Expression
	 * 
	 * @param e
	 * @return
	 * @implNote This function does not consider composed fillers. They can be only Datatypes
	 */
	@SuppressWarnings("unchecked")
	public static boolean isUniversalOfData(OWLClassExpression e) {
		if (!(e.getClassExpressionType() == ClassExpressionType.DATA_ALL_VALUES_FROM)) {
			return false;
		}
		
		OWLDataRange filler = ((OWLQuantifiedRestrictionImpl<OWLDataRange>) e).getFiller();

		if (!filler.isOWLDatatype()) {
			return false;
		}
		return true;
	}

}
