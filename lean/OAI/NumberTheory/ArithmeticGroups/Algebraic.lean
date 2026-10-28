import OAI.NumberTheory.ArithmeticGroups.CongruenceLevelL
import OAI.NumberTheory.ArithmeticGroups.AlgebraicDatum

/-! # Algebraic -/

namespace OAI.NumberTheory.ArithmeticGroups.Algebraic.CongruenceLevel

noncomputable section

/-! Bundle the integral form already proved to exist in CongruenceLevel. All hypotheses
of the algebraic construction are discharged here from the original datum. -/

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E]

def traceBilinear (b δ : E) : LinearMap.BilinForm ℚ (Data.CongruenceLevel.VE E) :=
  ∑ i : Fin 3, (AlgebraicGeometry.ComplexMultiplication.CM.TraceForm.cmTracePairing E (δ * (if i = 2 then b else 1))).flip.compl₁₂
    (LinearMap.proj i) (LinearMap.proj i)

theorem traceBilinear_apply (b δ : E) (x y : Data.CongruenceLevel.VE E) :
    traceBilinear b δ x y = Trace.CongruenceLevel.rationalTrace b δ x y := by
  change (∑ i : Fin 3, Algebra.trace ℚ E
    (δ * (if i = 2 then b else 1) * NumberField.IsCMField.complexConj E (y i) * x i)) = _
  simp only [Trace.CongruenceLevel.rationalTrace, Data.CongruenceLevel.hermitian, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

def integralRestriction {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = (n : ℚ)) :
    Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ := by
  let f : Λ → Λ → ℤ := fun x y => (h x x.property y y.property).choose
  have hf (x y : Λ) : (f x y : ℚ) = B x y :=
    (h x x.property y y.property).choose_spec.symm
  refine LinearMap.mk₂ ℤ f ?_ ?_ ?_ ?_
  · intro x y z
    apply Int.cast_injective (α := ℚ)
    simp only [Int.cast_add, hf]
    exact LinearMap.congr_fun (B.map_add x.val y.val) z.val
  · intro n x y
    apply Int.cast_injective (α := ℚ)
    simp only [zsmul_eq_mul, Int.cast_mul, hf]
    change B (n • x.val) y.val = (n : ℚ) * B x.val y.val
    rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  · intro x y z
    apply Int.cast_injective (α := ℚ)
    simp only [Int.cast_add, hf]
    exact (B x.val).map_add y.val z.val
  · intro n x y
    apply Int.cast_injective (α := ℚ)
    simp only [zsmul_eq_mul, Int.cast_mul, hf]
    change B x.val (n • y.val) = (n : ℚ) * B x.val y.val
    rw [map_zsmul, zsmul_eq_mul]

theorem integralRestriction_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = (n : ℚ)) (x y : Λ) :
    (integralRestriction B Λ h x y : ℚ) = B x y :=
  (h x x.property y y.property).choose_spec.symm

theorem integralRestriction_nondegenerate {V : Type*} [AddCommGroup V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V) (Λ : Submodule ℤ V)
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = (n : ℚ))
    (hspan : Submodule.span ℚ (Λ : Set V) = ⊤)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∀ x : Λ, (∀ y, integralRestriction B Λ h x y = 0) → x = 0 := by
  intro x hx
  apply Subtype.ext
  apply hnd x.val
  have hz : B x.val = 0 := by
    apply LinearMap.ext_on hspan
    intro y hy
    rw [← integralRestriction_apply B Λ h x ⟨y, hy⟩, hx, Int.cast_zero]
    rfl
  intro y
  exact LinearMap.congr_fun hz y

open OAI.NumberTheory.ArithmeticGroups.AlgebraicDatum.CongruenceLevel.Algebraic

theorem exists_admissible_reference_input
    {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ)
    (hσ : Function.Bijective
      (fun p : Place × Bool => if p.2 then AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (σ p.1) else σ p.1))
    (μ : Place) (b : E) (hb : NumberField.IsCMField.complexConj E b = b)
    (hb_nonzero : b ≠ 0) (hμ : (σ μ b).re < 0)
    (hcompact : ∀ τ, τ ≠ μ → 0 < (σ τ b).re) (dref : Place → Bool)
    (h : CongruenceLevelDatum.ReferenceDatum σ μ b dref) :
    ∃ P : AlgebraicDatum.CongruenceLevel.Algebraic.ReferenceInput E Place,
      P.embeddings = σ ∧ P.distinguished = μ ∧ P.b = b ∧ P.compactSigns = dref ∧
      P.IsAdmissible := by
  obtain ⟨δ, m, Λ, F, hδ, hδc, hm, hΛ, hint, halt, hnd, _, _, hhol, hfib, _⟩ := h
  let B := (m : ℚ) • traceBilinear b δ
  have hB (x y : Data.CongruenceLevel.VE E) : B x y = (m : ℚ) * Trace.CongruenceLevel.rationalTrace b δ x y := by
    change (m : ℚ) * traceBilinear b δ x y = _
    rw [traceBilinear_apply]
  have hi : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, B x y = (n : ℚ) := by
    simpa only [hB, Trace.CongruenceLevel.rationalTrace] using hint
  let P : AlgebraicDatum.CongruenceLevel.Algebraic.ReferenceInput E Place :=
    ⟨σ, μ, dref, b, δ, m, Λ, integralRestriction B Λ hi, F⟩
  refine ⟨P, rfl, rfl, rfl, rfl, hσ, hb, hb_nonzero, hμ, hcompact,
    hδ, hδc, hm, hΛ, ?_, ?_, ?_, hhol, hfib⟩
  · intro x y
    exact (integralRestriction_apply B Λ hi x y).trans (hB x y)
  · intro x
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_zero, integralRestriction_apply, hB]
    exact halt x.val
  · apply integralRestriction_nondegenerate B Λ hi hΛ.2.1
    simpa only [hB, Trace.CongruenceLevel.rationalTrace] using hnd

end

end OAI.NumberTheory.ArithmeticGroups.Algebraic.CongruenceLevel
