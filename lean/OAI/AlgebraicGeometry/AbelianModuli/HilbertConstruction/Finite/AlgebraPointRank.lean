import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Etale.Pi

/-! # Algebra Point Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AlgebraPointRank

noncomputable section

/-! A finite algebra whose field-valued point count equals its vector-space dimension is the product of those copies of the field. This detects the absence of infinitesimal length in finite geometric fibers. -/
universe u v

def algebraPointEvaluation (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] :
    B →ₐ[K] ((B →ₐ[K] K) → K) where
  toFun x φ := φ x
  map_one' := by ext φ; exact map_one φ
  map_mul' x y := by ext φ; exact map_mul φ x y
  map_zero' := by ext φ; exact map_zero φ
  map_add' x y := by ext φ; exact map_add φ x y
  commutes' x := by ext φ; exact φ.commutes x

theorem algebraPointEvaluation_injective_of_card_eq
    (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]
    (hcard : Nat.card (B →ₐ[K] K) = Module.finrank K B) :
    Function.Injective (algebraPointEvaluation K B) := by
  classical
  let : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  have hdim : Fintype.card (B →ₐ[K] K) = Module.finrank K (B →ₗ[K] K) :=
    (Nat.card_eq_fintype_card.symm.trans hcard).trans (Module.finrank_linearMap_self (R := K) (S := K) (M := B)).symm
  have hspan := (linearIndependent_algHom_toLinearMap K B K).span_eq_top_of_card_eq_finrank' hdim
  intro x y hxy
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff K (x - y)).mp
  intro φ
  have hφ : φ ∈ Submodule.span K (Set.range (AlgHom.toLinearMap : (B →ₐ[K] K) → B →ₗ[K] K)) :=
    hspan.symm ▸ Submodule.mem_top
  induction hφ using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      change a (x - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun hxy a)
  | zero => rfl
  | add a b _ _ ha hb => exact (congrArg₂ (· + ·) ha hb).trans (zero_add 0)
  | smul r a _ ha => exact (congrArg (r • ·) ha).trans (smul_zero r)

theorem algebraPointEvaluation_bijective_of_card_eq
    (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]
    (hcard : Nat.card (B →ₐ[K] K) = Module.finrank K B) :
    Function.Bijective (algebraPointEvaluation K B) := by
  classical
  let : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  have hi := algebraPointEvaluation_injective_of_card_eq K B hcard
  have hdim : Module.finrank K B = Module.finrank K ((B →ₐ[K] K) → K) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard]
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (algebraPointEvaluation K B).toLinearMap) hdim).mp hi⟩

def finiteAlgebraPointEquiv
    (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]
    (hcard : Nat.card (B →ₐ[K] K) = Module.finrank K B) : B ≃ₐ[K] ((B →ₐ[K] K) → K) :=
  AlgEquiv.ofBijective (algebraPointEvaluation K B) (algebraPointEvaluation_bijective_of_card_eq K B hcard)

theorem finiteAlgebra_reduced_of_point_card_eq
    (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]
    (hcard : Nat.card (B →ₐ[K] K) = Module.finrank K B) : IsReduced B :=
  isReduced_of_injective (algebraPointEvaluation K B)
    (algebraPointEvaluation_injective_of_card_eq K B hcard)

theorem finiteAlgebra_etale_of_point_card_eq
    (K : Type u) [Field K] (B : Type v) [CommRing B] [Algebra K B] [Module.Finite K B]
    (hcard : Nat.card (B →ₐ[K] K) = Module.finrank K B) : Algebra.Etale K B := by
  classical
  let : Fintype (B →ₐ[K] K) := Fintype.ofFinite _
  exact Algebra.Etale.of_equiv (finiteAlgebraPointEquiv K B hcard).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.AlgebraPointRank
