import OAI.RepresentationTheory.Hecke.RadialDilation.SplitTrace
import OAI.RepresentationTheory.Hecke.RadialDilation.PairedSymplectic

/-! # Split Paired Trace -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization

noncomputable section

section

/-! Pairing the local embedding blocks by CM conjugation. -/

open scoped Classical _root_.Matrix

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (K : Type*) [Field K] [Algebra ℚ K]

theorem conjugateSplitEmbedding_involutive (σ : E →ₐ[ℚ] K) :
    SplitTrace.Realization.conjugateSplitEmbedding E K (SplitTrace.Realization.conjugateSplitEmbedding E K σ) = σ := by
  ext x
  change σ (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x)) = σ x
  rw [AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply]

def splitPairingEmbeddings {Place : Type*} (σ : Place → E →ₐ[ℚ] K) :
    Place × Bool → (E →ₐ[ℚ] K) :=
  fun p => if p.2 then SplitTrace.Realization.conjugateSplitEmbedding E K (σ p.1) else σ p.1

def splitPairedFunctionEquiv {Place : Type*} (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (splitPairingEmbeddings E K σ)) :
    ((E →ₐ[ℚ] K) → Fin 3 → K) ≃ₗ[K] PairedSymplectic.Realization.SplitPairedSpace (K := K) (Place := Place) := by
  let e := Equiv.ofBijective (splitPairingEmbeddings E K σ) hσ
  refine
    { toFun := fun f τ => (f (σ τ), f (SplitTrace.Realization.conjugateSplitEmbedding E K (σ τ)))
      invFun := fun u ρ => if (e.symm ρ).2 then (u (e.symm ρ).1).2 else (u (e.symm ρ).1).1
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  · intro f
    funext ρ
    obtain ⟨⟨τ, b⟩, rfl⟩ := e.surjective ρ
    dsimp only
    rw [e.symm_apply_apply]
    cases b <;> rfl
  · intro u
    funext τ
    have hp : e.symm (σ τ) = (τ, false) := e.symm_apply_apply (τ, false)
    have hn : e.symm (SplitTrace.Realization.conjugateSplitEmbedding E K (σ τ)) = (τ, true) := e.symm_apply_apply (τ, true)
    simp only [hp, hn, Bool.false_eq_true, ↓reduceIte]

theorem split_normOne_conjugate_inverse (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1) (σ : E →ₐ[ℚ] K) :
    SplitTrace.Realization.conjugateSplitEmbedding E K σ (r : E) = (σ (r : E))⁻¹ := by
  have h := congrArg σ hr
  rw [map_mul, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem splitPairedFunctionEquiv_scalar {Place : Type*} (σ : Place → E →ₐ[ℚ] K)
    (hσ : Function.Bijective (splitPairingEmbeddings E K σ)) (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (u : (E →ₐ[ℚ] K) → Fin 3 → K) :
    splitPairedFunctionEquiv E K σ hσ (SplitScalarCoordinates.Realization.splitScalarEnd E K (r : E) u) =
      fun τ => (σ τ (r : E) • (splitPairedFunctionEquiv E K σ hσ u τ).1,
        (σ τ (r : E))⁻¹ • (splitPairedFunctionEquiv E K σ hσ u τ).2) := by
  funext τ
  apply Prod.ext
  · rfl
  · change SplitTrace.Realization.conjugateSplitEmbedding E K (σ τ) (r : E) • u (SplitTrace.Realization.conjugateSplitEmbedding E K (σ τ)) = _
    rw [split_normOne_conjugate_inverse E K r hr]
    rfl

def splitCrossMatrix {Place : Type*} (σ : Place → E →ₐ[ℚ] K)
    (θ : E) (H : Matrix (Fin 3) (Fin 3) E) (τ : Place) : Matrix (Fin 3) (Fin 3) K :=
  σ τ θ • H.map (σ τ)

omit [NumberField E] [NumberField.IsCMField E] in
theorem splitCrossMatrix_det_ne_zero {Place : Type*} (σ : Place → E →ₐ[ℚ] K)
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0) (τ : Place) :
    (splitCrossMatrix E K σ θ H τ).det ≠ 0 := by
  rw [splitCrossMatrix, Matrix.det_smul]
  have hdet : (H.map (σ τ)).det = σ τ H.det := ((σ τ).toRingHom.map_det H).symm
  rw [hdet]
  exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero (σ τ)).mpr hθ))
    ((map_ne_zero (σ τ)).mpr hH)

end

/-! The local trace form is the alternating sum of its CM-paired cross-pairings. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem matrix_cross_transpose {K : Type*} [CommRing K]
    (A : Matrix (Fin 3) (Fin 3) K) (u v : Fin 3 → K) :
    (∑ j, ∑ k, u j * A k j * v k) = ∑ j, ∑ k, v j * A j k * u k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrix_cross_smul {K : Type*} [Field K]
    (a : K) (A : Matrix (Fin 3) (Fin 3) K) (u v : Fin 3 → K) :
    u ⬝ᵥ ((a • A) *ᵥ v) = a * (∑ j, ∑ k, u j * A j k * v k) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (K : Type*) [Field K] [Algebra ℚ K]

theorem conjugateSplitEmbedding_apply (σ : E →ₐ[ℚ] K) (x : E) :
    SplitTrace.Realization.conjugateSplitEmbedding E K σ x = σ (NumberField.IsCMField.complexConj E x) := rfl

theorem splitTrace_paired_term (σ : E →ₐ[ℚ] K)
    (θ : E) (hθ : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (u v : (E →ₐ[ℚ] K) → Fin 3 → K) :
    (SplitTrace.Realization.conjugateSplitEmbedding E K σ θ *
      (∑ j, ∑ k, u (SplitTrace.Realization.conjugateSplitEmbedding E K σ) j *
        SplitTrace.Realization.conjugateSplitEmbedding E K σ (H j k) *
          v (SplitTrace.Realization.conjugateSplitEmbedding E K (SplitTrace.Realization.conjugateSplitEmbedding E K σ)) k)) +
      σ θ * (∑ j, ∑ k, u σ j * σ (H j k) * v (SplitTrace.Realization.conjugateSplitEmbedding E K σ) k) =
    u σ ⬝ᵥ ((σ θ • H.map σ) *ᵥ v (SplitTrace.Realization.conjugateSplitEmbedding E K σ)) -
      v σ ⬝ᵥ ((σ θ • H.map σ) *ᵥ u (SplitTrace.Realization.conjugateSplitEmbedding E K σ)) := by
  rw [conjugateSplitEmbedding_involutive, conjugateSplitEmbedding_apply, hθ, map_neg]
  have hentry (j k : Fin 3) : SplitTrace.Realization.conjugateSplitEmbedding E K σ (H j k) = σ (H k j) := by
    rw [conjugateSplitEmbedding_apply, ← hH k j]
  simp_rw [hentry]
  rw [matrix_cross_smul, matrix_cross_smul]
  simp only [Matrix.map_apply]
  have hswap := matrix_cross_transpose (H.map σ) (u (SplitTrace.Realization.conjugateSplitEmbedding E K σ)) (v σ)
  simp only [Matrix.map_apply] at hswap
  rw [hswap]
  ring

theorem splitTraceBilinear_paired {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] K) (hσ : Function.Bijective (splitPairingEmbeddings E K σ))
    (θ : E) (hθ : NumberField.IsCMField.complexConj E θ = -θ)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (u v : (E →ₐ[ℚ] K) → Fin 3 → K) :
    SplitTrace.Realization.splitTraceBilinear E K θ H u v =
      PairedSymplectic.Realization.pairedTraceValue (splitCrossMatrix E K σ θ H)
        (splitPairedFunctionEquiv E K σ hσ u) (splitPairedFunctionEquiv E K σ hσ v) := by
  let e := Equiv.ofBijective (splitPairingEmbeddings E K σ) hσ
  rw [SplitTrace.Realization.splitTraceBilinear_apply, ← Equiv.sum_comp e]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Fintype.sum_bool]
  exact splitTrace_paired_term E K (σ τ) θ hθ H hH u v

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization
