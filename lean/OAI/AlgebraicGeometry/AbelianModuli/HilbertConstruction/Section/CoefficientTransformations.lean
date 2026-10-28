import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion

/-! # Coefficient Transformations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientTransformations

noncomputable section

/-! Coefficient vectors form actual linear combinations of sheaf sections.
Changing the coefficient vectors by a linear map composes the corresponding
section map, including families that are not complete. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u v w
variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
variable (c : R →+* Γ(X, ⊤)) (M : X.Modules)

def coefficientSectionCombination (s : ι → (Line.Bundles.structureModule X ⟶ M)) (a : ι →₀ R) :
    Line.Bundles.structureModule X ⟶ M :=
  (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M).symm (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s a)

theorem coefficientSectionCombination_value (s : ι → (Line.Bundles.structureModule X ⟶ M)) (a : ι →₀ R) :
    Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M (coefficientSectionCombination c M s a) =
      Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s a :=
  (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M).apply_symm_apply _

theorem coefficientSectionCombination_single (s : ι → (Line.Bundles.structureModule X ⟶ M)) (i : ι) :
    coefficientSectionCombination c M s (Finsupp.single i 1) = s i := by
  apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M).injective
  exact (coefficientSectionCombination_value c M s _).trans
    (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single c M s i)

theorem coefficientSectionCombination_sum (s : ι → (Line.Bundles.structureModule X ⟶ M)) (a : ι →₀ R) :
    coefficientSectionCombination c M s a = ∑ i ∈ a.support, Scalar.SectionValues.scalarSection (c (a i)) (s i) := by
  apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M).injective
  rw [coefficientSectionCombination_value, map_sum]
  simp only [Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar]
  rfl

def transformSectionFamily (s : ι → (Line.Bundles.structureModule X ⟶ M)) (T : (κ →₀ R) →ₗ[R] (ι →₀ R)) :
    κ → (Line.Bundles.structureModule X ⟶ M) := fun i => coefficientSectionCombination c M s (T (Finsupp.single i 1))

private theorem freeCoefficientMap_reconstruct {V : Type*} [AddCommGroup V] [Module R V]
    (f : (κ →₀ R) →ₗ[R] V) :
    Finsupp.linearCombination R (fun i => f (Finsupp.single i 1)) = f := by
  apply Finsupp.lhom_ext
  intro i r
  rw [Finsupp.linearCombination_single, ← f.map_smul, Finsupp.smul_single', mul_one]

theorem transformSectionFamily_linearCombination (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (T : (κ →₀ R) →ₗ[R] (ι →₀ R)) :
    Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M (transformSectionFamily c M s T) =
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).comp T := by
  have hv : (fun i => Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M (transformSectionFamily c M s T i)) =
      fun i => (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).comp T (Finsupp.single i 1) := by
    funext i
    exact coefficientSectionCombination_value c M s _
  change Finsupp.linearCombination R _ = _
  rw [hv]
  exact freeCoefficientMap_reconstruct _

theorem coefficientSectionCombination_transform (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (T : (κ →₀ R) →ₗ[R] (ι →₀ R)) (a : κ →₀ R) :
    coefficientSectionCombination c M (transformSectionFamily c M s T) a =
      coefficientSectionCombination c M s (T a) := by
  apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M).injective
  rw [coefficientSectionCombination_value, coefficientSectionCombination_value,
    transformSectionFamily_linearCombination]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientTransformations
