import OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality

/-! # Product To -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo

noncomputable section

section

/-! The actual local cross product in normalized homology coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions.Pair OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality.Constructions

namespace Constructions.Normalization

abbrev normalSpace (d : ℕ) : TopCat.{0} := TopCat.of (Fin d → ℂ)

abbrev normalProductComplement (d c : ℕ) :=
  HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (normalSpace d) (normalSpace c) ({0}ᶜ) ({0}ᶜ)

theorem normalProductComplement_eq (d c : ℕ) : normalProductComplement d c = {0}ᶜ :=
  HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (normalSpace d) (normalSpace c) 0 0

theorem standardCross_generator (d c : ℕ) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates d c)
      (normalProductComplement d c) (normalProductComplement_eq d c)
      (2 * d + 2 * c) (Nat.mul_add 2 d c).symm
      (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (normalSpace d) (normalSpace c) ({0}ᶜ) ({0}ᶜ)
        (2 * d) (2 * c) (2 * d + 2 * c) rfl
        (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator d) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c)) =
      ProductHomologyCoefficient.Constructions.localProductCrossCoefficient d c := by
  rw [HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_apply]
  rfl

theorem standardHomology_decompose (d : ℕ)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (normalSpace d) ({0}ᶜ) (2 * d)) :
    Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv d a • Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator d = a := by
  apply (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv d).injective
  rw [map_smul, Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator_normalization, smul_eq_mul, mul_one]

theorem standardCross_normalization (d c : ℕ)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (normalSpace d) ({0}ᶜ) (2 * d))
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (normalSpace c) ({0}ᶜ) (2 * c)) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates d c)
      (normalProductComplement d c) (normalProductComplement_eq d c)
      (2 * d + 2 * c) (Nat.mul_add 2 d c).symm
      (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (normalSpace d) (normalSpace c) ({0}ᶜ) ({0}ᶜ)
        (2 * d) (2 * c) (2 * d + 2 * c) rfl a b) =
      ProductHomologyCoefficient.Constructions.localProductCrossCoefficient d c * Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv d a *
        Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyEquiv c b := by
  conv_lhs => rw [← standardHomology_decompose d a, ← standardHomology_decompose c b]
  rw [Relative.CrossNaturality.Constructions.relativeCrossClassAt_smul_left, Relative.CrossNaturality.Constructions.relativeCrossClassAt_smul_right, map_smul, map_smul,
    standardCross_generator]
  simp only [smul_eq_mul]
  ring

theorem standardCross_normalization_at (d c p q n : ℕ)
    (hp : p = 2 * d) (hq : q = 2 * c) (hn : n = 2 * (d + c)) (hpq : p + q = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (normalSpace d) ({0}ᶜ) p)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (normalSpace c) ({0}ᶜ) q) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates d c)
      (normalProductComplement d c) (normalProductComplement_eq d c) n hn
      (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (normalSpace d) (normalSpace c) ({0}ᶜ) ({0}ᶜ) p q n hpq a b) =
      ProductHomologyCoefficient.Constructions.localProductCrossCoefficient d c *
        HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (ContinuousLinearEquiv.refl ℂ (Fin d → ℂ)) ({0}ᶜ) rfl p hp a *
        HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (ContinuousLinearEquiv.refl ℂ (Fin c → ℂ)) ({0}ᶜ) rfl q hq b := by
  subst hp
  subst hq
  rw [Relative.CrossNaturality.Constructions.relativeCrossClassAt_cast]
  rw [HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_degreeMap _ _ _ _ _ (Nat.mul_add 2 d c).symm hn hpq]
  change _ = ProductHomologyCoefficient.Constructions.localProductCrossCoefficient d c *
    HomologyCoordinates.Constructions.coordinateHomologyEquiv (ContinuousLinearEquiv.refl ℂ (Fin d → ℂ)) a *
    HomologyCoordinates.Constructions.coordinateHomologyEquiv (ContinuousLinearEquiv.refl ℂ (Fin c → ℂ)) b
  rw [HomologyCoordinates.Constructions.Pair.coordinateHomologyEquiv_refl, HomologyCoordinates.Constructions.Pair.coordinateHomologyEquiv_refl]
  exact standardCross_normalization d c a b

end Constructions.Normalization

end

section

/-! Local cross-product normalization in arbitrary actual complex coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions.Pair
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo.Constructions.Normalization
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossNaturality.Constructions

namespace Constructions.CoordinateFormula

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem coordinateMapsTo {d : ℕ} (e : E ≃L[ℂ] (Fin d → ℂ)) (A : Set E) (hA : A = {0}ᶜ) :
    Set.MapsTo (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom A ({0}ᶜ) := by
  rw [hA]
  exact Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
theorem crossComplement_eq (A : Set E) (B : Set F) (hA : A = {0}ᶜ) (hB : B = {0}ᶜ) :
    HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of E) (TopCat.of F) A B = ({0}ᶜ : Set (E × F)) := by
  subst A
  subst B
  exact HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of E) (TopCat.of F) 0 0

theorem coordinateCross_normalization {d c : ℕ}
    (e : E ≃L[ℂ] (Fin d → ℂ)) (f : F ≃L[ℂ] (Fin c → ℂ))
    (eP : (E × F) ≃L[ℂ] (Fin (d + c) → ℂ))
    (A : Set E) (B : Set F) (hA : A = {0}ᶜ) (hB : B = {0}ᶜ)
    (p q n : ℕ) (hp : p = 2 * d) (hq : q = 2 * c) (hn : n = 2 * (d + c)) (hpq : p + q = n)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of E) A p)
    (b : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of F) B q) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv eP (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of E) (TopCat.of F) A B)
      (crossComplement_eq A B hA hB) n hn
      (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of E) (TopCat.of F) A B p q n hpq a b) =
      ProductHomologyCoefficient.Constructions.localProductCrossCoefficient d c * HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv e A hA p hp a *
        HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv f B hB q hq b := by
  have ht := HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_natural (e.prodCongr f) eP (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates d c)
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of E) (TopCat.of F) A B) (Normalization.normalProductComplement d c)
    (crossComplement_eq A B hA hB) (Normalization.normalProductComplement_eq d c) n hn
    (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.crossSupportComplement_mapsTo (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso f).hom
      (coordinateMapsTo e A hA) (coordinateMapsTo f B hB))
    (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of E) (TopCat.of F) A B p q n hpq a b)
  erw [Relative.CrossNaturality.Constructions.relativeCrossClassAt_natural ℚ (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom (Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso f).hom
    (coordinateMapsTo e A hA) (coordinateMapsTo f B hB)] at ht
  rw [Normalization.standardCross_normalization_at d c p q n hp hq hn hpq] at ht
  rw [HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_natural e e (ContinuousLinearEquiv.refl ℂ (Fin d → ℂ))
    A ({0}ᶜ) hA rfl p hp (coordinateMapsTo e A hA) a,
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_natural f f (ContinuousLinearEquiv.refl ℂ (Fin c → ℂ))
      B ({0}ᶜ) hB rfl q hq (coordinateMapsTo f B hB) b] at ht
  exact ht.symm

end Constructions.CoordinateFormula

end

section

/-! The two actual iterated local cross classes and their coordinate scalars. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleModels.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions.Pair
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo.Constructions.Normalization
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo.Constructions.CoordinateFormula OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociateForward.Constructions.HomologyAssociativity

namespace Constructions.TripleClasses

abbrev tripleDegree (a b c : ℕ) := (2 * a + 2 * b) + 2 * c
abbrev tripleNormalSpaces (a b c : ℕ) : TripleModels.Constructions.SpaceTriple := ((Normalization.normalSpace a, Normalization.normalSpace b), Normalization.normalSpace c)

abbrev leftComplement (a b c : ℕ) :=
  HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of ((Fin a → ℂ) × (Fin b → ℂ))) (Normalization.normalSpace c)
    (Normalization.normalProductComplement a b) ({0}ᶜ)

abbrev rightComplement (a b c : ℕ) :=
  HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (Normalization.normalSpace a) (TopCat.of ((Fin b → ℂ) × (Fin c → ℂ)))
    ({0}ᶜ) (Normalization.normalProductComplement b c)

theorem leftComplement_eq (a b c : ℕ) : leftComplement a b c = {0}ᶜ :=
  CoordinateFormula.crossComplement_eq (Normalization.normalProductComplement a b) ({0}ᶜ) (Normalization.normalProductComplement_eq a b) rfl

theorem rightComplement_eq (a b c : ℕ) : rightComplement a b c = {0}ᶜ :=
  CoordinateFormula.crossComplement_eq ({0}ᶜ) (Normalization.normalProductComplement b c) rfl (Normalization.normalProductComplement_eq b c)

def leftCoordinates (a b c : ℕ) :
    (((Fin a → ℂ) × (Fin b → ℂ)) × (Fin c → ℂ)) ≃L[ℂ] (Fin ((a + b) + c) → ℂ) :=
  ((HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates a b).prodCongr (ContinuousLinearEquiv.refl ℂ (Fin c → ℂ))).trans
    (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates (a + b) c)

def rightCoordinates (a b c : ℕ) :
    ((Fin a → ℂ) × ((Fin b → ℂ) × (Fin c → ℂ))) ≃L[ℂ] (Fin (a + (b + c)) → ℂ) :=
  ((ContinuousLinearEquiv.refl ℂ (Fin a → ℂ)).prodCongr (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates b c)).trans
    (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates a (b + c))

def leftTripleClass (a b c : ℕ) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of (((Fin a → ℂ) × (Fin b → ℂ)) × (Fin c → ℂ)))
      (leftComplement a b c) (tripleDegree a b c) :=
  Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (TopCat.of ((Fin a → ℂ) × (Fin b → ℂ))) (Normalization.normalSpace c)
    (Normalization.normalProductComplement a b) ({0}ᶜ) (2 * a + 2 * b) (2 * c) (tripleDegree a b c) rfl
    (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (Normalization.normalSpace a) (Normalization.normalSpace b) ({0}ᶜ) ({0}ᶜ)
      (2 * a) (2 * b) (2 * a + 2 * b) rfl
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator a) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator b))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c)

def rightTripleClass (a b c : ℕ) :
    Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of ((Fin a → ℂ) × ((Fin b → ℂ) × (Fin c → ℂ))))
      (rightComplement a b c) (tripleDegree a b c) :=
  Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (Normalization.normalSpace a) (TopCat.of ((Fin b → ℂ) × (Fin c → ℂ)))
    ({0}ᶜ) (Normalization.normalProductComplement b c) (2 * a) (2 * b + 2 * c) (tripleDegree a b c)
    (Nat.add_assoc (2 * a) (2 * b) (2 * c)).symm
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator a)
    (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (Normalization.normalSpace b) (Normalization.normalSpace c) ({0}ᶜ) ({0}ᶜ)
      (2 * b) (2 * c) (2 * b + 2 * c) rfl
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator b) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c))

theorem tripleClass_associative (a b c : ℕ) :
    leftTripleClass a b c =
      homologyMap (Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (TripleCross.Constructions.spaceAssociate (tripleNormalSpaces a b c)).inv
        (Relative.CrossAssociativity.Constructions.rightSupportMapsTo (tripleNormalSpaces a b c) ({0}ᶜ) ({0}ᶜ) ({0}ᶜ))) (tripleDegree a b c)
          (rightTripleClass a b c) :=
  Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt_associative ℚ (tripleNormalSpaces a b c) ({0}ᶜ) ({0}ᶜ) ({0}ᶜ)
    (2 * a) (2 * b) (2 * c) (tripleDegree a b c) rfl
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator a) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator b)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c)

theorem leftTripleClass_normalization (a b c : ℕ) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (leftCoordinates a b c) (leftComplement a b c)
      (leftComplement_eq a b c) (tripleDegree a b c) (by dsimp [tripleDegree]; omega)
      (leftTripleClass a b c) =
        ProductHomologyCoefficient.Constructions.localProductCrossCoefficient (a + b) c * ProductHomologyCoefficient.Constructions.localProductCrossCoefficient a b := by
  have h := CoordinateFormula.coordinateCross_normalization (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates a b)
    (ContinuousLinearEquiv.refl ℂ (Fin c → ℂ)) (leftCoordinates a b c)
    (Normalization.normalProductComplement a b) ({0}ᶜ) (Normalization.normalProductComplement_eq a b) rfl
    (2 * a + 2 * b) (2 * c) (tripleDegree a b c) (Nat.mul_add 2 a b).symm rfl
    (by dsimp [tripleDegree]; omega) rfl
    (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (Normalization.normalSpace a) (Normalization.normalSpace b) ({0}ᶜ) ({0}ᶜ)
      (2 * a) (2 * b) (2 * a + 2 * b) rfl
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator a) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator b))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c)
  rw [Normalization.standardCross_generator, HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_standard, mul_one] at h
  exact h

theorem rightTripleClass_normalization (a b c : ℕ) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (rightCoordinates a b c) (rightComplement a b c)
      (rightComplement_eq a b c) (tripleDegree a b c) (by dsimp [tripleDegree]; omega)
      (rightTripleClass a b c) =
        ProductHomologyCoefficient.Constructions.localProductCrossCoefficient a (b + c) * ProductHomologyCoefficient.Constructions.localProductCrossCoefficient b c := by
  have h := CoordinateFormula.coordinateCross_normalization (ContinuousLinearEquiv.refl ℂ (Fin a → ℂ))
    (HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates b c) (rightCoordinates a b c)
    ({0}ᶜ) (Normalization.normalProductComplement b c) rfl (Normalization.normalProductComplement_eq b c)
    (2 * a) (2 * b + 2 * c) (tripleDegree a b c) rfl (Nat.mul_add 2 b c).symm
    (by dsimp [tripleDegree]; omega) (Nat.add_assoc (2 * a) (2 * b) (2 * c)).symm
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator a)
    (Relative.CrossAssociateForward.Constructions.HomologyAssociativity.relativeCrossClassAt ℚ (Normalization.normalSpace b) (Normalization.normalSpace c) ({0}ᶜ) ({0}ᶜ)
      (2 * b) (2 * c) (2 * b + 2 * c) rfl
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator b) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator c))
  rw [Normalization.standardCross_generator, HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_standard, mul_one] at h
  exact h

end Constructions.TripleClasses

end

/-! The local product coefficient cocycle, proved from the actual relative
cross-product associativity and complex-linear coordinate invariance. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.CycleClass.Thom.TripleCross.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Relative.CrossAssociativity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.HomologyCoordinates.Constructions.Pair OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductHomologyCoefficient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo.Constructions.TripleClasses

namespace Constructions.Cocycle

def linearReassociate (a b c : ℕ) :
    (((Fin a → ℂ) × (Fin b → ℂ)) × (Fin c → ℂ)) ≃L[ℂ]
      ((Fin a → ℂ) × ((Fin b → ℂ) × (Fin c → ℂ))) :=
  ContinuousLinearEquiv.prodAssoc ℂ (Fin a → ℂ) (Fin b → ℂ) (Fin c → ℂ)

theorem tripleClass_normalization_associative (a b c : ℕ) :
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (TripleClasses.leftCoordinates a b c) (TripleClasses.leftComplement a b c)
      (TripleClasses.leftComplement_eq a b c) (TripleClasses.tripleDegree a b c) (by dsimp [TripleClasses.tripleDegree]; omega)
      (TripleClasses.leftTripleClass a b c) =
    HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv (TripleClasses.rightCoordinates a b c) (TripleClasses.rightComplement a b c)
      (TripleClasses.rightComplement_eq a b c) (TripleClasses.tripleDegree a b c) (by dsimp [TripleClasses.tripleDegree]; omega)
      (TripleClasses.rightTripleClass a b c) := by
  rw [TripleClasses.tripleClass_associative]
  have h := HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_natural (linearReassociate a b c).symm
    ((linearReassociate a b c).symm.trans (TripleClasses.leftCoordinates a b c)) (TripleClasses.leftCoordinates a b c)
    (TripleClasses.rightComplement a b c) (TripleClasses.leftComplement a b c)
    (TripleClasses.rightComplement_eq a b c) (TripleClasses.leftComplement_eq a b c)
    (TripleClasses.tripleDegree a b c) (by dsimp [TripleClasses.tripleDegree]; omega)
    (Relative.CrossAssociativity.Constructions.rightSupportMapsTo (TripleClasses.tripleNormalSpaces a b c) ({0}ᶜ) ({0}ᶜ) ({0}ᶜ)) (TripleClasses.rightTripleClass a b c)
  rw [HomologyCoordinates.Constructions.Pair.pairCoordinateHomologyEquiv_changeDimension (Nat.add_assoc a b c)
    ((linearReassociate a b c).symm.trans (TripleClasses.leftCoordinates a b c)) (TripleClasses.rightCoordinates a b c)
    (TripleClasses.rightComplement a b c) (TripleClasses.rightComplement_eq a b c) (TripleClasses.tripleDegree a b c)
    (by dsimp [TripleClasses.tripleDegree]; omega) (by dsimp [TripleClasses.tripleDegree]; omega)] at h
  exact h

theorem localProductCrossCoefficient_cocycle (a b c : ℕ) :
    ProductHomologyCoefficient.Constructions.localProductCrossCoefficient (a + b) c * ProductHomologyCoefficient.Constructions.localProductCrossCoefficient a b =
      ProductHomologyCoefficient.Constructions.localProductCrossCoefficient a (b + c) * ProductHomologyCoefficient.Constructions.localProductCrossCoefficient b c := by
  have h := tripleClass_normalization_associative a b c
  rw [TripleClasses.leftTripleClass_normalization, TripleClasses.rightTripleClass_normalization] at h
  exact h

theorem localProductCupCoefficient_cocycle (a b c : ℕ) :
    HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient a b * HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient (a + b) c =
      HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient b c * HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.localProductCupCoefficient a (b + c) := by
  have h := localProductCrossCoefficient_cocycle a b c
  simp only [ProductHomologyCoefficient.Constructions.localProductCrossCoefficient_eq_inv] at h
  have hi := congrArg Inv.inv h
  simpa only [mul_inv_rev, inv_inv] using hi

end Constructions.Cocycle

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductTo
