import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis

/-! # Pairing Transport -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization

noncomputable section

section

/-! Scalar extension of rational symplectic coordinates preserves the form. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.Matrix

def complexTraceForm {Place : Type*} [Fintype Place] (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin)
    (t : Place → ℂ) : LinearMap.BilinForm ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :=
  ∑ τ, t τ •
    let f := (B τ).compl₁₂
      ((LinearMap.fst ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec).comp (LinearMap.proj τ))
      ((LinearMap.snd ℂ Geometry.ComplexBall.PrescribedSignsB.Vec Geometry.ComplexBall.PrescribedSignsB.Vec).comp (LinearMap.proj τ))
    f - f.flip

theorem complexTraceForm_apply {Place : Type*} [Fintype Place]
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (t : Place → ℂ) (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    complexTraceForm B t u v = Geometry.ComplexBall.PrescribedSignsB.tracePairing (fun τ x y => B τ x y) t u v := by
  simp [complexTraceForm, Geometry.ComplexBall.PrescribedSignsB.tracePairing]

def coordinateBilinear {ι K : Type*} [Fintype ι] [Field K] :
    LinearMap.BilinForm K (Sum ι ι → K) := -Matrix.toBilin' (Matrix.J ι K)

theorem coordinateBilinear_apply {ι K : Type*} [Fintype ι] [Field K]
    (x y : Sum ι ι → K) : coordinateBilinear x y = FramePositivity.Realization.coordinatePairing x y := by
  simp only [coordinateBilinear, LinearMap.neg_apply, Matrix.toBilin'_apply',
    Matrix.J, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec,
    Matrix.one_mulVec, zero_add, add_zero, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Function.comp_def]
  simp only [FramePositivity.Realization.coordinatePairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib]
  ring

theorem rationalCoordinates_preserves_pairing
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {Place ι : Type*} [Fintype Place] [Fintype ι]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum ι ι → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E (δ * a) H x y)
    (u v : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    FramePositivity.Realization.coordinatePairing (RationalCoordinates.Realization.rationalCoordinates E σ hσ e u) (RationalCoordinates.Realization.rationalCoordinates E σ hσ e v) =
      Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB σ H) (fun τ => σ τ (δ * a)) u v := by
  let B := complexTraceForm (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a))
  let ec := RationalCoordinates.Realization.rationalCoordinates E σ hσ e
  change FramePositivity.Realization.coordinatePairing (ec u) (ec v) = _
  rw [← coordinateBilinear_apply]
  have hB (s t : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) : B s t =
      Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB σ H) (fun τ => σ τ (δ * a)) s t := by
    dsimp only [B]
    rw [complexTraceForm_apply]
    simp only [Geometry.ComplexBall.PrescribedSignsB.matrixB_apply]
  rw [← hB]
  obtain ⟨x, rfl⟩ := (Complexification.Realization.pairedComplexification E σ hσ).surjective u
  obtain ⟨y, rfl⟩ := (Complexification.Realization.pairedComplexification E σ hσ).surjective v
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul z x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      | tmul w y =>
          change coordinateBilinear
            (RationalCoordinates.Realization.rationalCoordinates E σ hσ e (Complexification.Realization.pairedComplexification E σ hσ (z ⊗ₜ[ℚ] x)))
            (RationalCoordinates.Realization.rationalCoordinates E σ hσ e (Complexification.Realization.pairedComplexification E σ hσ (w ⊗ₜ[ℚ] y))) = _
          rw [RationalCoordinates.Realization.rationalCoordinates_tmul, RationalCoordinates.Realization.rationalCoordinates_tmul,
            Complexification.Realization.pairedComplexification_tmul, Complexification.Realization.pairedComplexification_tmul]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
          congr 2
          rw [coordinateBilinear_apply, hB]
          have hh := SymplecticBasis.Realization.rationalTraceForm_realization E σ hσ δ a hδ ha H hH x y
          rw [← he] at hh
          rw [← hh]
          simp [FramePositivity.Realization.coordinatePairing]

end

/-! Rational norm-one multiplication gives an actual symplectic matrix. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem preserving_coordinatePairing_symplectic
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (M : Matrix (Sum ι ι) (Sum ι ι) K)
    (hM : ∀ x y, FramePositivity.Realization.coordinatePairing (M *ᵥ x) (M *ᵥ y) = FramePositivity.Realization.coordinatePairing x y) :
    M ∈ Matrix.symplecticGroup ι K := by
  have hb : (coordinateBilinear (ι := ι) (K := K)).comp M.toLin' M.toLin' =
      coordinateBilinear := by
    apply LinearMap.ext₂
    intro x y
    simpa only [LinearMap.BilinForm.comp_apply, coordinateBilinear_apply,
      Matrix.toLin'_apply] using hM x y
  have hm := congrArg LinearMap.BilinForm.toMatrix' hb
  simp only [LinearMap.BilinForm.toMatrix'_comp, coordinateBilinear,
    LinearMap.toMatrix'_toLin'] at hm
  have hn : LinearMap.BilinForm.toMatrix' (coordinateBilinear (ι := ι) (K := K)) =
      -Matrix.J ι K := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.BilinForm.toMatrix'_apply]
    rw [coordinateBilinear_apply]
    cases i <;> cases j <;>
      simp [FramePositivity.Realization.coordinatePairing, Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Pi.single_apply, eq_comm]
  change M.transpose * LinearMap.BilinForm.toMatrix' coordinateBilinear * M =
    LinearMap.BilinForm.toMatrix' coordinateBilinear at hm
  rw [hn, Matrix.mul_neg, Matrix.neg_mul] at hm
  exact SymplecticGroup.mem_iff'.mpr (neg_injective hm)

theorem rationalTraceForm_scalar_invariant
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (x y : Fin 3 → E) :
    SymplecticBasis.Realization.rationalTraceForm E (δ * a) H (Complexification.Realization.rationalScalarEnd E (r : E) x)
      (Complexification.Realization.rationalScalarEnd E (r : E) y) = SymplecticBasis.Realization.rationalTraceForm E (δ * a) H x y := by
  have hc (v : Fin 3 → E) : Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ (Complexification.Realization.rationalScalarEnd E (r : E) v) =
      fun τ => Archimedean.Realization.pairedScalar (σ τ (r : E)) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ v τ) := by
    funext τ
    exact Archimedean.Realization.embeddingCoordinates_scalar E r hr σ v τ
  have hn (τ : Place) : σ τ (r : E) ≠ 0 := (map_ne_zero (σ τ)).mpr (Units.ne_zero r)
  have hh := Archimedean.Realization.scalar_preserves_tracePairing (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) (fun τ => σ τ (δ * a))
    (fun τ => σ τ (r : E)) hn (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y)
  simp only [Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] at hh
  have hcast : (SymplecticBasis.Realization.rationalTraceForm E (δ * a) H (Complexification.Realization.rationalScalarEnd E (r : E) x)
      (Complexification.Realization.rationalScalarEnd E (r : E) y) : ℂ) = (SymplecticBasis.Realization.rationalTraceForm E (δ * a) H x y : ℂ) := by
    rw [SymplecticBasis.Realization.rationalTraceForm_realization E σ hσ δ a hδ ha H hH,
      SymplecticBasis.Realization.rationalTraceForm_realization E σ hσ δ a hδ ha H hH, hc, hc]
    exact hh
  exact_mod_cast hcast

theorem rationalScalarMatrix_symplectic
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {Place ι : Type*} [Fintype Place] [Fintype ι] [DecidableEq ι]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum ι ι → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E (δ * a) H x y)
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1) :
    RationalCoordinates.Realization.rationalScalarMatrix E e (r : E) ∈ Matrix.symplecticGroup ι ℚ := by
  apply preserving_coordinatePairing_symplectic
  intro v w
  obtain ⟨x, rfl⟩ := e.surjective v
  obtain ⟨y, rfl⟩ := e.surjective w
  rw [RationalCoordinates.Realization.rationalScalarMatrix_apply, RationalCoordinates.Realization.rationalScalarMatrix_apply, he, he]
  exact rationalTraceForm_scalar_invariant E σ hσ δ a hδ ha H hH r hr x y

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization
