import OAI.RepresentationTheory.Hecke.GeometricParameters

/-! # Theta Arithmetic -/

namespace OAI.NumberTheory.PadicHodge.ThetaArithmetic.FrobeniusSlope

noncomputable section

/-! Exact retained GaloisValuation witnesses and their raw-kernel sign convention. -/

open scoped Classical TensorProduct _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E] (q : ℕ) [Fact q.Prime]
  (ιE : E →ₐ[ℚ] RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)
  (ι : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* AlgebraicClosure ℚ_[q])
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (reps : Finset Gal(E/ℚ)) (r : Eˣ) (M : ℕ) (ωc ζc : ℂ)

/-- The complete body of GaloisValuation's conclusion, with its witnesses exposed. -/
def ParameterData (χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
    (Ω Ζ a e : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) (β : Fin 3 → RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ) : Prop :=
  let j := RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE
  let ν := RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι
  let s := RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j
  j Ω = ωc ∧ j Ζ = ζc ∧ a ≠ 0 ∧ a ^ M = Ω ∧ e = a⁻¹ ∧
  (∃ n : ℕ, 0 < n ∧ Ζ ^ n = 1) ∧
  Ω ^ 2 = Ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
  RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => (β i : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s e) ∧
  (∀ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = χ (1 ⊗ₜ[ℚ] T)) ∧
  (∀ σ : Gal(RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ), ‖j (σ e)‖ = 1) ∧
  ν e = (-3 / 2 : ℚ) ∧
  (ν e = (-3 / 2 : ℚ) ∨ ν e = (3 / 2 : ℚ)) ∧
  ∀ σ : Gal(RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ),
    (∀ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, σ (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (β i)) T) ∧
    ν (σ e) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * ν e ∧
    (∃ eσ : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar,
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s eσ)) ∧
    (∀ eσ : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar,
      RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
        (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple s eσ) →
      (eσ = σ e ∨ eσ = -(σ e)) ∧
      ν eσ = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * ν e)

theorem parameterConclusion_iff (χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) :
    RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.ParameterConclusion E q ιE ι v reps r M ωc ζc χ ↔
      ∃ Ω Ζ a e β, ParameterData E q ιE ι v reps r M ωc ζc χ Ω Ζ a e β := Iff.rfl

/-- Inverse-coset normalization uses e=a⁻¹; the actual raw parameter is a. -/
theorem retained_raw_signs (χ : RepresentationTheory.Hecke.SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
    (Ω Ζ a e : RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) (β : Fin 3 → RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ)
    (h : ParameterData E q ιE ι v reps r M ωc ζc χ Ω Ζ a e β) :
    (∀ σ : Gal(RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ),
      ‖RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (σ a)‖ = 1) ∧
    RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι a = (3 / 2 : ℚ) ∧
    ∀ σ : Gal(RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ), RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι (σ a) =
      (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * (3 / 2 : ℚ) := by
  obtain ⟨_, _, ha, _, he, _, _, _, _, hunit, hbase, _, hgal⟩ := h
  have hinv (σ : Gal(RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ)) :
      RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι (σ e) = -RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι (σ a) := by
    rw [he, map_inv₀]
    exact RepresentationTheory.Hecke.GaloisValuationCm.val_inv _ (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_mul q ι) _
      ((map_ne_zero σ).mpr ha)
  refine ⟨?_, ?_, ?_⟩
  · intro σ
    have hu := hunit σ
    rw [he, map_inv₀, map_inv₀, norm_inv] at hu
    exact (inv_eq_one.mp hu)
  · rw [he, RepresentationTheory.Hecke.GaloisValuationCm.val_inv _ (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_mul q ι) a ha] at hbase
    linarith
  · intro σ
    have hs := (hgal σ).2.1
    rw [hinv, hbase] at hs
    linarith

end

end OAI.NumberTheory.PadicHodge.ThetaArithmetic.FrobeniusSlope
