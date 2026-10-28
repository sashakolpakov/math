import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Cochain Model Homotopy -/

namespace OAI.AlgebraicTopology.Kunneth.CochainModelHomotopy

noncomputable section

/-! Acyclic-model factorization for functionals, used by the multiplicative comparison. -/

set_option backward.isDefEq.respectTransparency false

namespace Constructions

variable {K : Type*} [Field K]

/-- A functional vanishing on a kernel factors through the linear map. -/
theorem functional_factor {A B : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (d : A →ₗ[K] B) (L : A →ₗ[K] K)
    (h : LinearMap.ker d ≤ LinearMap.ker L) :
    ∃ H : B →ₗ[K] K, H.comp d = L := by
  let f : LinearMap.range d →ₗ[K] K :=
    ((LinearMap.ker d).liftQ L h).comp d.quotKerEquivRange.symm.toLinearMap
  obtain ⟨H, hH⟩ := f.exists_extend
  refine ⟨H, ?_⟩
  apply LinearMap.ext
  intro a
  have he := LinearMap.congr_fun hH (d.rangeRestrict a)
  change H (d a) = _ at he ⊢
  rw [he]
  dsimp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hq : d.quotKerEquivRange.symm (d.rangeRestrict a) = (LinearMap.ker d).mkQ a := by
    apply d.quotKerEquivRange.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact (d.quotKerEquivRange_apply_mk a).symm
  rw [hq]
  rfl

/-- Local exactness builds a comparison homotopy one degree at a time.
Here `δ` is the alternating face operator on linear functionals. -/
theorem modelFunctionalHomotopy
    (V : ℕ → ℕ → Type*) [∀ n p, AddCommGroup (V n p)] [∀ n p, Module K (V n p)]
    (d : ∀ n p, V n p →ₗ[K] V n (p + 1))
    (δ : ∀ n p, (V n p →ₗ[K] K) →ₗ[K] (V (n + 1) p →ₗ[K] K))
    (hex : ∀ n p (a : V n (p + 1)), d n (p + 1) a = 0 →
      ∃ b : V n p, d n p b = a)
    (hδd : ∀ n p (H : V n (p + 1) →ₗ[K] K),
      δ n p (H.comp (d n p)) = (δ n (p + 1) H).comp (d (n + 1) p))
    (hδδ : ∀ n p (H : V n p →ₗ[K] K), δ (n + 1) p (δ n p H) = 0)
    (q : ℕ) (L : ∀ p, V (q + p) p →ₗ[K] K)
    (hL : ∀ p, (L (p + 1)).comp (d (q + p + 1) p) = δ (q + p) p (L p))
    (hzero : LinearMap.ker (d q 0) ≤ LinearMap.ker (L 0)) :
    ∃ H : ∀ p, V (q + p) (p + 1) →ₗ[K] K,
      (H 0).comp (d q 0) = L 0 ∧
      ∀ p, (H (p + 1)).comp (d (q + p + 1) (p + 1)) =
        L (p + 1) - δ (q + p) (p + 1) (H p) := by
  let Invariant (p : ℕ) (H : V (q + p) (p + 1) →ₗ[K] K) : Prop :=
    δ (q + p) p (H.comp (d (q + p) p)) = δ (q + p) p (L p)
  have step (p : ℕ) (H : V (q + p) (p + 1) →ₗ[K] K) (hH : Invariant p H) :
      ∃ H' : V (q + p + 1) (p + 1 + 1) →ₗ[K] K,
        H'.comp (d (q + p + 1) (p + 1)) = L (p + 1) - δ (q + p) (p + 1) H := by
    apply functional_factor
    intro a ha
    obtain ⟨b, rfl⟩ := hex (q + p + 1) p a ha
    change L (p + 1) (d (q + p + 1) p b) -
      δ (q + p) (p + 1) H (d (q + p + 1) p b) = 0
    have h₁ := LinearMap.congr_fun (hL p) b
    have h₂ := LinearMap.congr_fun (hδd (q + p) p H) b
    have h₃ := LinearMap.congr_fun hH b
    change L (p + 1) (d (q + p + 1) p b) = δ (q + p) p (L p) b at h₁
    change δ (q + p) p (H.comp (d (q + p) p)) b =
      δ (q + p) (p + 1) H (d (q + p + 1) p b) at h₂
    rw [h₁, ← h₂]
    exact sub_eq_zero.mpr h₃.symm
  obtain ⟨H₀, hH₀⟩ := functional_factor (d q 0) (L 0) hzero
  let Stage (p : ℕ) := {H : V (q + p) (p + 1) →ₗ[K] K // Invariant p H}
  let initial : Stage 0 := ⟨H₀, by change δ q 0 (H₀.comp (d q 0)) = _; rw [hH₀]; rfl⟩
  let next (p : ℕ) (H : Stage p) : Stage (p + 1) :=
    ⟨(step p H.val H.property).choose, by
      change δ (q + p + 1) (p + 1)
          (((step p H.val H.property).choose).comp (d (q + p + 1) (p + 1))) = _
      rw [(step p H.val H.property).choose_spec, map_sub, hδδ, sub_zero]
      rfl⟩
  let stages : ∀ p, Stage p := Nat.rec initial next
  refine ⟨fun p => (stages p).val, hH₀, ?_⟩
  intro p
  exact (step p (stages p).val (stages p).property).choose_spec

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.CochainModelHomotopy
