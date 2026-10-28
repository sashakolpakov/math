import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Section Frame Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion

noncomputable section

/-! A specified section family is complete precisely when its actual
coefficient linear-combination map is bijective. The inverse map constructs
the basis and retains the given sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type v}
variable (c : R →+* Γ(X, ⊤)) (M : X.Modules)

def coefficientSectionLinearCombination (s : ι → (Line.Bundles.structureModule X ⟶ M)) :
    (ι →₀ R) →ₗ[R] (GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M :=
  Finsupp.linearCombination R (fun i => RingSectionBasis.coefficientRingSectionAddEquiv c M (s i))

theorem coefficientSectionLinearCombination_single
    (s : ι → (Line.Bundles.structureModule X ⟶ M)) (i : ι) :
    coefficientSectionLinearCombination c M s (Finsupp.single i 1) =
      RingSectionBasis.coefficientRingSectionAddEquiv c M (s i) := by
  exact (Finsupp.linearCombination_single R 1 i).trans (one_smul R _)

def coefficientSectionBasisOfBijective (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (h : Function.Bijective (coefficientSectionLinearCombination c M s)) :
    Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (coefficientSectionLinearCombination c M s) h).symm

theorem coefficientSectionBasisOfBijective_family (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (h : Function.Bijective (coefficientSectionLinearCombination c M s)) :
    RingSectionBasis.coefficientRingBasisFamily c M (coefficientSectionBasisOfBijective c M s h) = s := by
  funext i
  apply (RingSectionBasis.coefficientRingSectionAddEquiv c M).injective
  change RingSectionBasis.coefficientRingSectionAddEquiv c M
    ((RingSectionBasis.coefficientRingSectionAddEquiv c M).symm
      (coefficientSectionLinearCombination c M s (Finsupp.single i 1))) = _
  exact (AddEquiv.apply_symm_apply _ _).trans
    (coefficientSectionLinearCombination_single c M s i)

theorem coefficientSectionLinearCombination_basis
    (b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M)) :
    coefficientSectionLinearCombination c M (RingSectionBasis.coefficientRingBasisFamily c M b) =
      b.repr.symm.toLinearMap := by
  have hv : (fun i => RingSectionBasis.coefficientRingSectionAddEquiv c M (RingSectionBasis.coefficientRingBasisFamily c M b i)) = b := by
    funext i
    exact (RingSectionBasis.coefficientRingSectionAddEquiv c M).apply_symm_apply (b i)
  change Finsupp.linearCombination R _ = _
  rw [hv]
  exact b.coe_repr_symm.symm

theorem coefficientSectionLinearCombination_bijective_iff
    (s : ι → (Line.Bundles.structureModule X ⟶ M)) :
    Function.Bijective (coefficientSectionLinearCombination c M s) ↔
      ∃ b : Module.Basis ι R ((GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M),
        RingSectionBasis.coefficientRingBasisFamily c M b = s := by
  constructor
  · intro h
    exact ⟨coefficientSectionBasisOfBijective c M s h,
      coefficientSectionBasisOfBijective_family c M s h⟩
  · rintro ⟨b, rfl⟩
    rw [coefficientSectionLinearCombination_basis]
    exact b.repr.symm.bijective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionFrameCriterion
