import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalMultiplicity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding

/-! # Equation Thom Residue -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EquationThomResidue.Constructions

noncomputable section

section

/-!
# DegreeTwo: an actual equation's supported winding is the local Thom generator

When the normal pair was constructed with the equation as its coordinate,
the supported winding class has the proved universal Thom normalization.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding

variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (h : C(X, ℂ)) (x : X) (hx : h x = 0)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ (Subtype.val : {y : X // h y = 0} → X) ⟨x, hx⟩)

/-- The actual defining function, restricted to the complement of its
full zero locus in the genuine normal neighborhood. -/
def equationComplementFunction : C(P.relativeComplement, ℂ) :=
  h.comp ⟨fun y => y.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

omit [NormedSpace ℝ E] in
theorem equationComplementFunction_ne_zero (y : P.relativeComplement) :
    equationComplementFunction h x hx P y ≠ 0 := by
  intro hy
  exact y.property ⟨⟨y.val.val, hy⟩, rfl⟩

omit [NormedSpace ℝ E] in
/-- The actual equation has the proved signed logarithmic residue. -/
theorem equation_supportedWindingClass_eq_neg_residue
    (hP : ∀ y : P.neighborhood, P.normalCoordinate y = h y.val) :
    DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) P.relativeComplement
      (equationComplementFunction h x hx P) (equationComplementFunction_ne_zero h x hx P) =
      -NormalResidue.Constructions.normalLogarithmicResidue P := by
  let g := NormalResidue.Constructions.ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo
  have hg : ∀ y, g y ≠ 0 := fun y =>
    (NormalResidue.Constructions.ExponentialCocycle.nonzeroRestriction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo y).property
  have heq : equationComplementFunction h x hx P = g := by
    apply ContinuousMap.ext
    intro y
    exact (hP y.val).symm
  calc
    _ = DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) P.relativeComplement g hg :=
      DivisorClass.Chern.Supported.Winding.supportedWindingClass_congr _ _ _ _ _ hg heq
    _ = -NormalResidue.Constructions.normalLogarithmicResidue P := DivisorClass.Chern.Supported.Winding.supportedWindingClass_logarithmic _ _ g hg

/-- The actual equation's supported class is the normalized local Thom
class, with the sign inherited from the proved Cech winding convention. -/
theorem equation_supportedWindingClass_eq_Thom
    (hP : ∀ y : P.neighborhood, P.normalCoordinate y = h y.val) :
    DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) P.relativeComplement
      (equationComplementFunction h x hx P) (equationComplementFunction_ne_zero h x hx P) =
      (-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • NormalMultiplicity.Constructions.normalChartClass P := by
  rw [equation_supportedWindingClass_eq_neg_residue h x hx P hP,
    NormalMultiplicity.Constructions.normalLogarithmicResidue_eq_chartClass, neg_smul]

theorem equation_supportedWindingClass_ne_zero
    (hP : ∀ y : P.neighborhood, P.normalCoordinate y = h y.val) :
    DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) P.relativeComplement
      (equationComplementFunction h x hx P) (equationComplementFunction_ne_zero h x hx P) ≠ 0 := by
  rw [equation_supportedWindingClass_eq_neg_residue h x hx P hP]
  exact neg_ne_zero.mpr (NormalResidue.Constructions.normalLogarithmicResidue_ne_zero P)

end

/-!
# DegreeTwo: equation residues after enlarging the closed support

The reference divisor can contain components not present in a chosen local
equation. Shrinking the complement sends the already-normalized equation
residue to the corresponding image of the actual local Thom class.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding

variable {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  (h : C(X, ℂ)) (x : X) (hx : h x = 0)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ (Subtype.val : {y : X // h y = 0} → X) ⟨x, hx⟩)

/-- The defining equation restricted to any smaller complement. -/
def equationOnSubspace (A : Set P.neighborhood) : C(A, ℂ) :=
  h.comp ⟨fun y => y.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

omit [NormedSpace ℝ E] in
theorem equationOnSubspace_ne_zero (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement)
    (y : A) : equationOnSubspace h x hx P A y ≠ 0 := by
  intro hy
  exact hA y.property ⟨⟨y.val.val, hy⟩, rfl⟩

/-- The local equation retains its actual Thom coefficient when the
closed support is enlarged, by the genuine map of relative pairs. -/
theorem equation_supportedWindingClass_support_extension
    (hP : ∀ y : P.neighborhood, P.normalCoordinate y = h y.val)
    (A : Set P.neighborhood) (hA : A ⊆ P.relativeComplement) :
    DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) A
      (equationOnSubspace h x hx P A) (equationOnSubspace_ne_zero h x hx P A hA) =
      (-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (𝟙 (TopCat.of P.neighborhood)) hA 2 (NormalMultiplicity.Constructions.normalChartClass P) := by
  have hn := DivisorClass.Chern.Supported.Winding.supportedWindingClass_pullback (TopCat.of P.neighborhood) P.relativeComplement
    (𝟙 (TopCat.of P.neighborhood)) A hA
    (equationComplementFunction h x hx P) (equationComplementFunction_ne_zero h x hx P)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of P.neighborhood)) hA 2
      (DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) P.relativeComplement
        (equationComplementFunction h x hx P) (equationComplementFunction_ne_zero h x hx P)) =
    DivisorClass.Chern.Supported.Winding.supportedWindingClass (TopCat.of P.neighborhood) A
      (equationOnSubspace h x hx P A) (equationOnSubspace_ne_zero h x hx P A hA) at hn
  rw [equation_supportedWindingClass_eq_Thom h x hx P hP, map_smul] at hn
  exact hn.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EquationThomResidue.Constructions
