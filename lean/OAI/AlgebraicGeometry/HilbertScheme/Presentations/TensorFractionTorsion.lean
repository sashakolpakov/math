import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.DegreeShift
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Tensor Fraction Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion.GradedModules

noncomputable section

/-! Polynomial-power torsion dies in localized tensor products. -/

universe u v w t

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

def moduleScalarEnd (a : A) : M →ₗ[R] M :=
  (algebraMap A (Module.End A M) a).restrictScalars R

theorem moduleFractionMap_scalar (a b : A) (k : ℕ) :
    (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k).comp (moduleScalarEnd (R := R) M b) =
      (Localized.DegreeShift.GradedModules.localizedScalarEnd (R := R) (M := M) a b).comp (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k) := by
  apply LinearMap.ext
  intro m
  change Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k (b • m) = b • Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) a k m
  rw [Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, Presentations.Module.Fractions.GradedModules.moduleFractionMap_apply, LocalizedModule.smul'_mk]

theorem tensorFraction_zero_of_power_torsion (g b c : A) (h : g = b * c)
    (S : Type t) [AddCommGroup S] [Module R S]
    (x : TensorProduct R S M) (k : ℕ)
    (hx : ((moduleScalarEnd (R := R) M (b ^ k)).lTensor S) x = 0) :
    ((Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) g 0).lTensor S) x = 0 := by
  let E := Localized.DegreeShift.GradedModules.localizedScalarPowerEquiv (R := R) (M := M) g b c h k
  apply (E.lTensor S).injective
  rw [map_zero]
  change ((Localized.DegreeShift.GradedModules.localizedScalarEnd (R := R) (M := M) g (b ^ k)).lTensor S)
    (((Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) g 0).lTensor S) x) = 0
  rw [← LinearMap.lTensor_comp_apply, ← moduleFractionMap_scalar,
    LinearMap.lTensor_comp_apply, hx, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorFractionTorsion.GradedModules
