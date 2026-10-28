import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanSpace
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Dense Hilbert -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.DenseHilbert.Construction

noncomputable section

/-! A bounded conjugate-linear functional on a dense linear test space
has a unique Hilbert-space representative. This is a proved construction
from the continuous extension and the Riesz isometry. -/

open scoped InnerProductSpace ComplexConjugate

variable {S H : Type*} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (P : S →ₗ[ℂ] H) (hP : DenseRange P)

include hP

omit [CompleteSpace H] in
theorem eq_of_dense_test_pairings (v w : H)
    (h : ∀ f : S, ⟪P f, v⟫_ℂ = ⟪P f, w⟫_ℂ) : v = w := by
  have hh (x : H) : ⟪x, v⟫_ℂ = ⟪x, w⟫_ℂ := by
    have hs : IsClosed {y : H | ⟪y, v⟫_ℂ = ⟪y, w⟫_ℂ} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hr : Set.range P ⊆ {y : H | ⟪y, v⟫_ℂ = ⟪y, w⟫_ℂ} := by
      rintro y ⟨f, rfl⟩
      exact h f
    apply closure_minimal hr hs
    rw [hP.closure_range]
    trivial
  have hz : ⟪v - w, v - w⟫_ℂ = 0 := by
    rw [inner_sub_right, hh, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_vector_of_bounded_conjugate_linear
    (L : S → ℂ) (hadd : ∀ f h, L (f + h) = L f + L h)
    (hsmul : ∀ (z : ℂ) f, L (z • f) = conj z * L f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ f, ‖L f‖ ≤ C * ‖P f‖) :
    ∃ v : H, ‖v‖ ≤ C ∧ ∀ f : S, ⟪P f, v⟫_ℂ = L f := by
  let A : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => conj (L f)
      map_add' := fun f h => by rw [hadd, map_add]
      map_smul' := fun z f => by
        rw [hsmul, map_mul, starRingEnd_self_apply]
        rfl }
  have hA (f : S) : ‖A f‖ ≤ C * ‖P f‖ := by
    change ‖conj (L f)‖ ≤ _
    rw [RCLike.norm_conj]
    exact hbound f
  let T := A.extendOfNorm P
  have hT (f : S) : T (P f) = conj (L f) := LinearMap.extendOfNorm_eq hP ⟨C, hA⟩ f
  have hTnorm : ‖T‖ ≤ C := by
    apply T.opNorm_le_bound hC
    exact LinearMap.norm_extendOfNorm_apply_le hP C hA
  let v := (InnerProductSpace.toDual ℂ H).symm T
  refine ⟨v, ?_, fun f => ?_⟩
  · exact ((InnerProductSpace.toDual ℂ H).symm.norm_map T).trans_le hTnorm
  · rw [← inner_conj_symm]
    change conj ⟪(InnerProductSpace.toDual ℂ H).symm T, P f⟫_ℂ = L f
    rw [InnerProductSpace.toDual_symm_apply, hT, starRingEnd_self_apply]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.DenseHilbert.Construction
