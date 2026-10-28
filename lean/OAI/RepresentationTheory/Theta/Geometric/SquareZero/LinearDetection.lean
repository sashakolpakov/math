import Mathlib.RingTheory.DualNumber
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-! # Linear Detection -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearDetection

noncomputable section

/-! Ordinary complex dual-number quotients jointly detect a split
square-zero extension with an arbitrary complex coefficient space. -/

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M]

theorem squareZero_linear_quotients_jointly_injective (x y : TrivSqZeroExt ℂ M)
    (h : ∀ l : M →ₗ[ℂ] ℂ, TrivSqZeroExt.map l x = TrivSqZeroExt.map l y) : x = y := by
  apply TrivSqZeroExt.ext
  · simpa only [TrivSqZeroExt.fst_map] using congrArg TrivSqZeroExt.fst (h 0)
  · apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff ℂ (x.snd - y.snd)).mp
    intro l
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [TrivSqZeroExt.snd_map] using congrArg TrivSqZeroExt.snd (h l)

theorem squareZero_algebra_maps_ext {A : Type*} [CommRing A] [Algebra ℂ A]
    (f g : A →ₐ[ℂ] TrivSqZeroExt ℂ M)
    (h : ∀ l : M →ₗ[ℂ] ℂ, (TrivSqZeroExt.map l).comp f = (TrivSqZeroExt.map l).comp g) : f = g := by
  apply AlgHom.ext
  intro a
  apply squareZero_linear_quotients_jointly_injective
  intro l
  exact DFunLike.congr_fun (h l) a

theorem squareZero_ring_maps_ext {A : Type*} [CommRing A]
    (f g : A →+* TrivSqZeroExt ℂ M)
    (h : ∀ l : M →ₗ[ℂ] ℂ, (TrivSqZeroExt.map l).toRingHom.comp f =
      (TrivSqZeroExt.map l).toRingHom.comp g) : f = g := by
  apply RingHom.ext
  intro a
  apply squareZero_linear_quotients_jointly_injective
  intro l
  exact DFunLike.congr_fun (h l) a

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearDetection
