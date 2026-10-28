import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModelExtension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientUpperBounds

/-! # Smooth Affine Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAffineModels

noncomputable section

/-! Finitely many smooth affine algebras have smooth models over a common noetherian base. -/

universe u v

variable (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ i, Algebra.Smooth R (A i)]

theorem exists_common_smoothAffineModels (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ D : Subalgebra ℤ R, C ≤ D ∧ Algebra.FiniteType ℤ D ∧ IsNoetherianRing D ∧
      ∃ M : ∀ i, HilbertConstruction.Smooth.AffineModels.SmoothAffineModel R (A i), ∀ i, (M i).coefficients = D := by
  let M₀ (i : ι) : HilbertConstruction.Smooth.AffineModels.SmoothAffineModel R (A i) := (HilbertConstruction.Smooth.AffineModels.smoothAffineModel_nonempty R (A i)).some
  obtain ⟨D₀, hD₀, hbound⟩ := HilbertConstruction.Finite.CoefficientUpperBounds.exists_finiteType_coefficient_upperBound
    (fun i => (M₀ i).coefficients)
    (fun i => (Subalgebra.fg_iff_finiteType (M₀ i).coefficients).mpr inferInstance)
  let D := C ⊔ D₀
  have hfg : D.FG := ((Subalgebra.fg_iff_finiteType C).mpr inferInstance).sup hD₀
  have : Algebra.FiniteType ℤ D := (Subalgebra.fg_iff_finiteType D).mp hfg
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℤ D
  refine ⟨D, le_sup_left, inferInstance, inferInstance, ?_⟩
  exact ⟨fun i => (M₀ i).extend D ((hbound i).trans le_sup_right), fun _ => rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAffineModels
