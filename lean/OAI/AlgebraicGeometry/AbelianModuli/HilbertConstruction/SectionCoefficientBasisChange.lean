import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionTensorScalarMap
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Section Coefficient Basis Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionCoefficientBasisChange

noncomputable section

/-! The basis of the free coefficient module identifies the scalar
extension of specified sections with the actual coefficient map of their
pulled-back section family, including the full new-ring scalar action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct
universe u v
variable {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable (a : Y ⟶ X) (c : R →+* Γ(X, ⊤)) (M : X.Modules) (q : B →+* Γ(Y, ⊤))
variable (hq : q.comp (algebraMap R B) = a.appTop.hom.comp c)
variable {κ : Type v}

def freeCoefficientBaseChangeEquiv : (B ⊗[R] (κ →₀ R)) ≃ₗ[B] (κ →₀ B) :=
  ((Finsupp.basisSingleOne : Module.Basis κ R (κ →₀ R)).baseChange B).repr

theorem freeCoefficientBaseChangeEquiv_symm_single (i : κ) :
    (freeCoefficientBaseChangeEquiv (R := R) (B := B)).symm (Finsupp.single i 1) =
      (1 : B) ⊗ₜ[R] Finsupp.single i 1 := by
  change ((Finsupp.basisSingleOne : Module.Basis κ R (κ →₀ R)).baseChange B).repr.symm
    (Finsupp.single i 1) = _
  rw [Module.Basis.repr_symm_single_one, Module.Basis.baseChange_apply]
  rfl

theorem pulledSectionCoefficientMap_baseChange
    (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    (Coefficient.SectionTensorScalarMap.coefficientSectionTensorScalarMap a c M q hq).comp
        ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).baseChange B) =
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
        (fun i => Ample.LineBundles.pullbackSection a (s i))).comp freeCoefficientBaseChangeEquiv.toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (freeCoefficientBaseChangeEquiv (R := R) (B := B) (κ := κ)).symm.surjective z
  have he : (Coefficient.SectionTensorScalarMap.coefficientSectionTensorScalarMap a c M q hq).comp
      (((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).baseChange B).comp
        freeCoefficientBaseChangeEquiv.symm.toLinearMap) =
      Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
        (fun i => Ample.LineBundles.pullbackSection a (s i)) := by
    apply Finsupp.lhom_ext
    intro i b
    have hx : Finsupp.single i b = b • Finsupp.single i (1 : B) := by
      rw [Finsupp.smul_single', mul_one]
    rw [hx, map_smul, map_smul]
    apply congrArg (fun w => b • w)
    change Coefficient.SectionTensorScalarMap.coefficientSectionTensorScalarMap a c M q hq
      (((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).baseChange B)
        (freeCoefficientBaseChangeEquiv.symm (Finsupp.single i 1))) = _
    rw [freeCoefficientBaseChangeEquiv_symm_single]
    change Coefficient.SectionTensorScalarMap.coefficientSectionTensorScalarMap a c M q hq
      ((1 : B) ⊗ₜ[R] Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s (Finsupp.single i 1)) = _
    rw [Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single, Coefficient.SectionTensorScalarMap.coefficientSectionTensorScalarMap_section,
      one_smul, Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single]
  exact (LinearMap.congr_fun he x).trans
    (congrArg (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q ((Scheme.Modules.pullback a).obj M)
      (fun i => Ample.LineBundles.pullbackSection a (s i)))
        (freeCoefficientBaseChangeEquiv.apply_symm_apply x).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionCoefficientBasisChange
