import OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity
import OAI.RepresentationTheory.Hecke.RadialDilation.RealStructure
import OAI.RepresentationTheory.Weil.UnitarySplitting.SymplecticCoordinates

/-! # Symplectic Basis -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization

noncomputable section

section

/-! The rational trace form behind the concrete period construction. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.Matrix

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

def conjugateVector : (Fin 3 → E) →ₗ[ℚ] (Fin 3 → E) :=
  LinearMap.pi (fun i => (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E).toLinearMap.comp (LinearMap.proj i))

def rationalTraceForm (θ : E) (H : Matrix (Fin 3) (Fin 3) E) :
    LinearMap.BilinForm ℚ (Fin 3 → E) :=
  (((Matrix.toBilin' H).restrictScalars₁₂ ℚ ℚ).compl₂ (conjugateVector E)).compr₂
    ((Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ θ))

theorem rationalTraceForm_apply (θ : E) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → E) :
    rationalTraceForm E θ H x y = Algebra.trace ℚ E
      (θ * (∑ j, ∑ k, x j * H j k * NumberField.IsCMField.complexConj E (y k))) := by
  simp [rationalTraceForm, conjugateVector, Matrix.toBilin'_apply,
    AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation, Finset.mul_sum, mul_assoc]

theorem rationalTraceForm_realization {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (x y : Fin 3 → E) :
    (rationalTraceForm E (δ * a) H x y : ℂ) =
      Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB σ H) (fun τ => σ τ (δ * a))
        (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ x) (Geometry.ComplexBall.PrescribedSignsB.embeddingCoordinates σ y) := by
  rw [rationalTraceForm_apply]
  exact (Geometry.ComplexBall.PrescribedSignsB.tracePairing_rational σ hσ δ a hδ ha H hH x y).symm

theorem rationalTraceForm_alternating {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j)) :
    (rationalTraceForm E (δ * a) H).IsAlt := by
  intro x
  have hc : (rationalTraceForm E (δ * a) H x x : ℂ) = 0 := by
    rw [rationalTraceForm_realization E σ hσ δ a hδ ha H hH]
    simp [Geometry.ComplexBall.PrescribedSignsB.tracePairing]
  exact_mod_cast hc

theorem rationalTraceForm_apply_dot (θ : E) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → E) :
    rationalTraceForm E θ H x y = Algebra.trace ℚ E
      (θ * (x ⬝ᵥ (H *ᵥ conjugateVector E y))) := by
  simp [rationalTraceForm, Matrix.toBilin'_apply']

theorem conjugateVector_involutive : Function.Involutive (conjugateVector E) := by
  intro x
  funext i
  exact AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E (x i)

/-- Nondegeneracy uses the actual field trace, not a coordinate assumption. -/
theorem rationalTraceForm_left_nondegenerate
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (x : Fin 3 → E) (hx : ∀ y, rationalTraceForm E θ H x y = 0) : x = 0 := by
  have hsurj : Function.Surjective H.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det H).mpr (isUnit_iff_ne_zero.mpr hH))
  funext i
  have hi : θ * x i = 0 := by
    apply (traceForm_nondegenerate ℚ E).1
    intro t
    obtain ⟨z, hz⟩ := hsurj (Pi.single i t)
    have h := hx (conjugateVector E z)
    rw [rationalTraceForm_apply_dot, conjugateVector_involutive E, hz,
      dotProduct_single] at h
    change Algebra.trace ℚ E ((θ * x i) * t) = 0
    simpa only [mul_assoc] using h
  exact (mul_eq_zero.mp hi).resolve_left hθ

theorem rationalTraceForm_nondegenerate
    (θ : E) (hθ : θ ≠ 0) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0)
    (hAlt : (rationalTraceForm E θ H).IsAlt) :
    (rationalTraceForm E θ H).Nondegenerate := by
  constructor
  · exact rationalTraceForm_left_nondegenerate E θ hθ H hH
  · intro x hx
    apply rationalTraceForm_left_nondegenerate E θ hθ H hH x
    intro y
    rw [← hAlt.neg_eq y x, hx y, neg_zero]

end

/-! Existence of rational symplectic coordinates of the required size. -/

open scoped Classical _root_.Matrix TensorProduct
open _root_.Matrix

def swappedSumCoordinates {ι : Type*} (n : ℕ) (b : ι ≃ Fin n) :
    Weil.UnitarySplitting.SymplecticCoordinates.Coordinates ℚ n ≃ₗ[ℚ] (Sum ι ι → ℚ) where
  toFun x := Sum.elim (fun i => x.2 (b i)) (fun i => x.1 (b i))
  invFun x := (fun i => x (Sum.inr (b.symm i)), fun i => x (Sum.inl (b.symm i)))
  left_inv x := by ext i <;> simp
  right_inv x := by funext i; cases i <;> simp
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' c x := by funext i; cases i <;> rfl

theorem swappedSumCoordinates_pairing {ι : Type*} [Fintype ι]
    (n : ℕ) (b : ι ≃ Fin n) (x y : Weil.UnitarySplitting.SymplecticCoordinates.Coordinates ℚ n) :
    FramePositivity.Realization.coordinatePairing (swappedSumCoordinates n b x) (swappedSumCoordinates n b y) =
      Weil.UnitarySplitting.SymplecticCoordinates.coordinatePairing n x y := by
  exact Equiv.sum_comp b (fun i => x.2 i * y.1 i - x.1 i * y.2 i)

theorem exists_rational_symplectic_coordinates
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    {Place : Type*} [Fintype Place]
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a) (hδa : δ * a ≠ 0)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (hH : H.det ≠ 0) :
    ∃ e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) → ℚ),
      ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = rationalTraceForm E (δ * a) H x y := by
  have hAlt := rationalTraceForm_alternating E σ hσ δ a hδ ha H hHerm
  have hNondeg := rationalTraceForm_nondegenerate E (δ * a) hδa H hH hAlt
  obtain ⟨n, e₀, he₀⟩ := Weil.UnitarySplitting.SymplecticCoordinates.exists_coordinates _ hAlt hNondeg
  have hdim₀ := e₀.finrank_eq
  have hdim₁ := (Complexification.Realization.pairedComplexification E σ hσ).finrank_eq
  change Module.finrank ℂ (ℂ ⊗[ℚ] (Fin 3 → E)) = Module.finrank ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place) at hdim₁
  rw [Module.finrank_baseChange] at hdim₁
  have hn : Fintype.card (FramePositivity.Realization.FrameIndex Place) = n := by
    simp only [Weil.UnitarySplitting.SymplecticCoordinates.Coordinates, Module.finrank_prod,
      Module.finrank_pi, Fintype.card_fin] at hdim₀
    simp [Geometry.ComplexBall.PrescribedSignsB.Ambient, Geometry.ComplexBall.PrescribedSignsB.Vec, Module.finrank_pi_fintype, Module.finrank_prod] at hdim₁
    simp only [FramePositivity.Realization.FrameIndex, Fintype.card_prod, Fintype.card_fin]
    simp [Module.finrank_pi_fintype] at hdim₀
    omega
  let b : FramePositivity.Realization.FrameIndex Place ≃ Fin n := Fintype.equivOfCardEq (by simpa using hn)
  refine ⟨e₀.trans (swappedSumCoordinates n b), ?_⟩
  intro x y
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, swappedSumCoordinates_pairing]
  exact (he₀ x y).symm

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization
