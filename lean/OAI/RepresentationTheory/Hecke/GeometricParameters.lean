import OAI.RepresentationTheory.Hecke.IntrinsicAuxiliaryDilation
import OAI.RepresentationTheory.Hecke.IntrinsicFamily
import OAI.RepresentationTheory.Hecke.IntrinsicParameters

/-! # Geometric Parameters -/

namespace OAI.RepresentationTheory.Hecke.GeometricParameters.GaloisValuation

noncomputable section

/-! The valuation rule for a fixed complete native auxiliary-dilation witness. -/

open scoped Classical TensorProduct _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E] (q : ℕ) [Fact q.Prime]
  (ιE : E →ₐ[ℚ] IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)
  (ι : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* AlgebraicClosure ℚ_[q])
  (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (reps : Finset Gal(E/ℚ)) (r : Eˣ) (M : ℕ) (ωc ζc : ℂ)

/-- Parameters for the specified r, M, omega, phase and actual character.
No scalar or exponent is reselected in this conclusion. -/
def ParameterConclusion (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) : Prop :=
  let j := IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE
  let ν := IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι
  let s := IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j
  ∃ Ω Ζ a e : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar, ∃ β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ,
    j Ω = ωc ∧ j Ζ = ζc ∧ a ≠ 0 ∧ a ^ M = Ω ∧ e = a⁻¹ ∧
    (∃ n : ℕ, 0 < n ∧ Ζ ^ n = 1) ∧
    Ω ^ 2 = Ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) ∧
    GaloisValuationCm.ProjectivelyEqual (fun i => (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (GaloisValuationCm.parameterTriple s e) ∧
    (∀ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = χ (1 ⊗ₜ[ℚ] T)) ∧
    (∀ σ : Gal(IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ), ‖j (σ e)‖ = 1) ∧
    ν e = (-3 / 2 : ℚ) ∧
    (ν e = (-3 / 2 : ℚ) ∨ ν e = (3 / 2 : ℚ)) ∧
    ∀ σ : Gal(IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ),
      (∀ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, σ (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) =
        AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (β i)) T) ∧
      ν (σ e) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * ν e ∧
      (∃ eσ : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar,
        GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
          (GaloisValuationCm.parameterTriple s eσ)) ∧
      (∀ eσ : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar,
        GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
          (GaloisValuationCm.parameterTriple s eσ) →
        (eσ = σ e ∨ eσ = -(σ e)) ∧
        ν eσ = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * ν e)

/-- Extract the Galois-valuation root with the exact auxiliary-dilation scalar,
then apply the numerical parameter identity and the full rational-structure transport. -/
theorem parameters_of_same_dilation
    (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (hv : v.val 1 = true) (ha : (1 : Gal(E/ℚ)) ∈ reps)
    (hp : ∀ τ : Gal(E/ℚ), τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1) (hM : 0 < M)
    (hsplit : ∀ τ : Gal(E/ℚ), IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι (ιE (τ (r : E))) =
      if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
    (hζ : RadialDilation.Cm.finitePhase ζc)
    (hrel : ωc ^ 2 = ζc * ∏ τ ∈ reps,
      AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
    (hω : RadialDilation.Cm.algebraicUnitCircle ωc)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V) (θ : SphericalActionModelInverse.Radial q →ₗ[ℂ] V)
    (hSatake : SphericalActionModelInverse.RadialSatakeConclusion q .inverseCoset ρ θ M ωc)
    (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
    (hocc : ∃ x : V, x ∈ LinearMap.range θ ∧ x ≠ 0 ∧ ∀ h, ρ h x = χ h • x) :
    ParameterConclusion E q ιE ι v reps r M ωc ζc χ := by
  let j := IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE
  let ν := IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι
  have hj (x : E) : j (ιE x) = (x : ℂ) :=
    IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding_spec ιE E.val.toRingHom x
  obtain ⟨Ω, Ζ, hΩj, hΖj, hΖ, hprod, hΩ⟩ :=
    IntrinsicArithmetic.GaloisValuationIntrinsic.lift_dilation_parameters E j ιE hj reps r
      (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (-1) ωc ζc hζ hω
      (by simpa only [neg_one_mul] using hrel)
  obtain ⟨ac, hac, hrootc, _, α, hχα, hα⟩ := hSatake.2.2 χ hocc
  obtain ⟨a, e, haj, hej, hroot, _, hunit⟩ :=
    IntrinsicArithmetic.GaloisValuationIntrinsic.lift_dilation_root j Ω M hM hΩ ac ac⁻¹
      (by rw [hΩj]; exact hrootc) (Or.inr rfl)
  have ha0 : a ≠ 0 := by
    intro hz
    exact hac (by rw [← haj, hz, map_zero])
  have he : e = a⁻¹ := j.injective (by rw [hej, map_inv₀, haj])
  have he0 : e ≠ 0 := he ▸ inv_ne_zero ha0
  have hα' : SphericalActionModelInverse.ProjectivelyEqual (fun i => (α i : ℂ))
      (fun i => j (GaloisValuationCm.parameterTriple (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) e i)) := by
    convert hα using 1
    funext i
    fin_cases i <;> simp [GaloisValuationCm.parameterTriple, IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_image,
      hej, SphericalActionModelInverse.parameterForConvention]
  obtain ⟨β, hβ, hχβ, hconjβ⟩ := IntrinsicParameters.GaloisValuationIntrinsic.lift_actual_satake q hRationalStructure j
    (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) e (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_ne_zero q j) he0 χ α hχα hα'
  have hnum := GaloisValuationCm.galois_sign_rule_for_parameter_valuations
    E ιE (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE) (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction_commutes E ιE)
    v hv (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl) reps ha hp
    q (Fact.out : q.Prime) M hM r hr ν
    (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_mul q ι) (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_add q ι)
    (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_q q ι) hsplit a e Ω Ζ (-1) (Or.inr rfl)
    hΖ hprod hroot (Or.inr he) j.toRatAlgHom hunit
    (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_sq q j)
    (fun σ i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
    (IntrinsicParameters.GaloisValuationIntrinsic.projective_scalar_conjugate β (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) e hβ)
  have hbase : ν a = (3 / 2 : ℚ) := by
    have hh := GaloisValuationCm.dilation_root_valuation ιE (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE)
      (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction_commutes E ιE) (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_ne_one E)
      (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E) (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
      (GaloisValuationCm.inverse_sign_odd E v _ (fun _ => rfl)) reps hp r M hM ν
      (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_mul q ι) hsplit a Ω Ζ ha0 (-1) hΖ hprod hroot 1
    simpa [hv, AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue] using hh
  refine ⟨Ω, Ζ, a, e, β, hΩj, hΖj, ha0, hroot, he, hΖ, ?_, hβ, hχβ,
    hunit, ?_, hnum.1, ?_⟩
  · simpa only [neg_one_mul] using hprod
  · change ν e = (-3 / 2 : ℚ)
    rw [he, GaloisValuationCm.val_inv ν (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_mul q ι) a ha0, hbase]
    norm_num
  · intro σ
    exact ⟨hconjβ σ, by simpa only [inv_inv] using hnum.2 σ⟩

end

end OAI.RepresentationTheory.Hecke.GeometricParameters.GaloisValuation
