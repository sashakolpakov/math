import OAI.RepresentationTheory.Hecke.IntrinsicSatake
import OAI.RepresentationTheory.Hecke.IntrinsicArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange
import OAI.RepresentationTheory.Hecke.GaloisValuationCm

/-! # Intrinsic Parameters -/

namespace OAI.RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic

noncomputable section

section

/-! Transfer the complete SphericalAction parameter, including its actual Satake
character, into the same chosen algebraic closure as the CM scalar. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.SphericalActionModelInverse OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa

lemma lift_projective_triple (j : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* ℂ) (s e : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)
    (hs : s ≠ 0) (he : e ≠ 0) (α : Fin 3 → ℂˣ)
    (hα : SphericalActionModelInverse.ProjectivelyEqual (fun i => (α i : ℂ))
      (fun i => j (GaloisValuationCm.parameterTriple s e i))) :
    ∃ β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ,
      GaloisValuationCm.ProjectivelyEqual (fun i => (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (GaloisValuationCm.parameterTriple s e) ∧
      ∃ z : ℂˣ, α = fun i => z * Units.map j.toMonoidHom (β i) := by
  obtain ⟨z, hz, p, hp⟩ := hα
  let β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ := fun i =>
    (![Units.mk0 s hs, (Units.mk0 s hs)⁻¹, Units.mk0 e he] : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ) (p i)
  have hβ (i : Fin 3) : (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) = GaloisValuationCm.parameterTriple s e (p i) := by
    dsimp [β, GaloisValuationCm.parameterTriple]
    generalize p i = k
    fin_cases k <;> rfl
  refine ⟨β, ⟨1, one_ne_zero, p, fun i => by rw [one_mul]; exact hβ i⟩,
    Units.mk0 z hz, ?_⟩
  funext i
  apply Units.ext
  change (α i : ℂ) = z * j (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)
  rw [hβ]
  exact hp i

lemma lift_actual_satake (q : ℕ) [Fact q.Prime]
    (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (j : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* ℂ) (s e : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) (hs : s ≠ 0) (he : e ≠ 0)
    (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) (α : Fin 3 → ℂˣ)
    (hχα : SphericalActionModelInverse.HasSatakeParameter q χ α)
    (hα : SphericalActionModelInverse.ProjectivelyEqual (fun i => (α i : ℂ))
      (fun i => j (GaloisValuationCm.parameterTriple s e i))) :
    ∃ β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ,
      GaloisValuationCm.ProjectivelyEqual (fun i => (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (GaloisValuationCm.parameterTriple s e) ∧
      (∀ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
        j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = χ (1 ⊗ₜ[ℚ] T)) ∧
      ∀ (σ : Gal(IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ)) (T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q),
        σ (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) =
          AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (β i)) T := by
  obtain ⟨β, hβ, z, hz⟩ := lift_projective_triple j s e hs he α hα
  refine ⟨β, hβ, ?_, ?_⟩
  · intro T
    change j.toRatAlgHom (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = _
    rw [IntrinsicSatake.GaloisValuationIntrinsic.satake_map q hRationalStructure j.toRatAlgHom]
    have hh : χ (1 ⊗ₜ[ℚ] T) = AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q α T := by
      rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_complex]
      exact DFunLike.congr_fun hχα _
    rw [hh, hz, AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver_scale]
    rfl
  · intro σ T
    exact IntrinsicSatake.GaloisValuationIntrinsic.satake_map q hRationalStructure σ.toAlgHom β T

lemma projective_scalar_conjugate (β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ) (s e : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)
    (hβ : GaloisValuationCm.ProjectivelyEqual (fun i => (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (GaloisValuationCm.parameterTriple s e))
    (σ : Gal(IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ)) :
    GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
      (fun i => σ (GaloisValuationCm.parameterTriple s e i)) := by
  obtain ⟨z, hz, p, hp⟩ := hβ
  refine ⟨σ z, (map_ne_zero σ).mpr hz, p, ?_⟩
  intro i
  simpa only [map_mul] using congrArg σ (hp i)

end

/-! GaloisValuation with complete RadialDilation/SphericalAction/RationalStructure inputs, on the native radial action.
The Galois restriction and both closure embeddings are constructed. The
valuation is the rationally normalized valuation of the q-adic algebraic
closure. Its only local arithmetic premise is the prescribed orders of r
at the completely split embedding, the manuscript's input from (2).
-/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.RepresentationTheory.Hecke.SphericalActionModelInverse OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E] (q : ℕ) [Fact q.Prime]
  (ιE : E →ₐ[ℚ] IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar) (f : E →+* ℚ_[q])

def complexEmbedding : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* ℂ := IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding ιE E.val.toRingHom

def padicClosureEmbedding : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar →+* AlgebraicClosure ℚ_[q] :=
  IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding ιE ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f)

def valuation : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar → ℚ := IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q (padicClosureEmbedding E q ιE f)

omit [IsGalois ℚ E] [NumberField.IsCMField E] in
theorem valuation_on_field (x : E) : GaloisValuationIntrinsic.valuation E q ιE f (ιE x) = (f x).valuation := by
  unfold GaloisValuationIntrinsic.valuation IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation padicClosureEmbedding
  rw [IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding_spec]
  exact NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation_algebraMap q (f x)

/-- The complete original numerical conclusion on the actual conjugated
algebraic torus points, together with their character and root identities. -/
def NativeConclusion
    (d : Gal(E/ℚ) → ℤ) (reps : Finset Gal(E/ℚ)) (r : Eˣ) (M : ℕ) (ε : ℤ)
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (θ : SphericalActionModelInverse.Radial q →ₗ[ℂ] V) (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ) : Prop :=
  let j := complexEmbedding E ιE
  let ν := GaloisValuationIntrinsic.valuation E q ιE f
  let s := IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j
  ∃ ω ζ e₀ e : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar, ∃ β : Fin 3 → IntrinsicArithmetic.GaloisValuationIntrinsic.Qbarˣ,
    (∀ b, θ ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b) = j ω • θ b) ∧
    (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
    ω ^ 2 = ζ * ∏ τ ∈ reps, (ιE (τ (r : E))) ^ (ε * 3 * d τ) ∧
    e₀ ^ M = ω ∧ (e = e₀ ∨ e = e₀⁻¹) ∧
    GaloisValuationCm.ProjectivelyEqual (fun i => (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar)) (GaloisValuationCm.parameterTriple s e) ∧
    (∀ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, j (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = χ (1 ⊗ₜ[ℚ] T)) ∧
    (ν e = (-3 / 2 : ℚ) ∨ ν e = (3 / 2 : ℚ)) ∧
    ∀ σ : Gal(IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar/ℚ),
      (∀ T : Theta.Geometric.SphericalGU.Spherical.SL3Hecke q, σ (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) =
        AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q (fun i => Units.map σ.toMonoidHom (β i)) T) ∧
      ν (σ e) = (d ((IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)⁻¹) : ℚ) * ν e ∧
      (∃ eσ : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar, GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
        (GaloisValuationCm.parameterTriple s eσ)) ∧
      (∀ eσ : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar, GaloisValuationCm.ProjectivelyEqual (fun i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
        (GaloisValuationCm.parameterTriple s eσ) →
        (eσ = σ e ∨ eσ = -(σ e)) ∧
        ν eσ = (d ((IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)⁻¹) : ℚ) * ν e)

/-- Apply the full RadialDilation and SphericalAction propositions to one common theta map,
then derive the root-choice and RationalStructure scalar-equivariance clauses. -/
theorem native_parameters_of_normalized_inputs
    (hRadialDilation : GaloisValuationIntrinsic.Intrinsic.RadialDilation.Proposition.{0, 0})
    (hSphericalAction : GaloisValuationIntrinsic.Intrinsic.SphericalAction.Proposition.{0})
    (hRationalStructure : GaloisValuationIntrinsic.Intrinsic.RationalStructure.Proposition.{0})
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true) (d : Gal(E/ℚ) → ℤ)
    (hd : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (reps : Finset Gal(E/ℚ)) (hactive : (1 : Gal(E/ℚ)) ∈ reps)
    (hpair : ∀ τ : Gal(E/ℚ), τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (M : ℕ) (hM : 0 < M)
    (horders : ∀ τ : Gal(E/ℚ), (f (τ (r : E))).valuation =
      if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℤ) else if τ = 1 then -(M : ℤ) else 0)
    (S V : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
    (jrad : RadialDilation.Cm.radialInput q →ₗ[ℂ] S) (hjrad : Function.Injective jrad)
    (Θ : S →ₗ[ℂ] V) (U : S →ₗ[ℂ] S)
    (Uq : RadialDilation.Cm.radialInput q →ₗ[ℂ] RadialDilation.Cm.radialInput q)
    (hUq : ∀ b x, (Uq b).val x =
      (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
        b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i))
    (ξ : ℂ) (hξ : RadialDilation.Cm.finitePhase ξ)
    (hfinite : ∀ b, U (jrad b) = ξ • jrad (Uq b))
    (halfDet : ℂ)
    (hdet : halfDet ^ 2 = (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E)) ^ (1 - 2 : ℤ) *
      ∏ τ ∈ reps.erase 1, (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ))
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hPoisson : ∀ x : S, Θ (U x) =
      ((halfDet * (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-ε)) • Θ x)
    (c : SphericalActionModelInverse.ActingConvention) (ρV : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V)
    (hGeometricTheta : ∀ h b, Θ (jrad (SphericalActionModelInverse.radialAction q c h b)) = ρV h (Θ (jrad b)))
    (χ : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] ℂ)
    (hocc : ∃ x : V, x ∈ LinearMap.range (Θ.comp jrad) ∧ x ≠ 0 ∧
      ∀ h, ρV h x = χ h • x) :
    NativeConclusion E q ιE f d reps r M ε (Θ.comp jrad) χ := by
  let j := complexEmbedding E ιE
  let ν := GaloisValuationIntrinsic.valuation E q ιE f
  have hj (x : E) : j (ιE x) = (x : ℂ) := IntrinsicArithmetic.GaloisValuationIntrinsic.extendAlgebraicEmbedding_spec ιE E.val.toRingHom x
  obtain ⟨_, ωc, ζc, hζc, hθ, hrelc, hωc, _⟩ :=
    hRadialDilation E v hv d hd reps hactive hpair r hr q M hM S V jrad hjrad Θ U
      (RadialDilation.Mem.Realization.dilation q) Uq (RadialDilation.Mem.Realization.dilation_apply q) hUq ξ hξ hfinite halfDet hdet ε hε hPoisson
  have hωnorm : ‖ωc‖ = 1 := hωc.2 ωc (minpoly.aeval ℚ ωc)
  have hθ' : ∀ b, (Θ.comp jrad) ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b) = ωc • (Θ.comp jrad) b := by
    intro b
    simpa only [LinearMap.comp_apply, AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation.dilationEquiv_pow_apply] using hθ b
  have hSphericalActionout := hSphericalAction q c V ρV (Θ.comp jrad) M hM ωc hωnorm hGeometricTheta hθ'
  obtain ⟨e₀c, he₀c, hrootc, _, α, hχα, hα⟩ := hSphericalActionout.2.2 χ hocc
  have hec : SphericalActionModelInverse.parameterForConvention c e₀c = e₀c ∨ SphericalActionModelInverse.parameterForConvention c e₀c = e₀c⁻¹ := by
    cases c <;> simp [SphericalActionModelInverse.parameterForConvention]
  obtain ⟨ω, ζ, hωj, _, hζ, hrel, hω⟩ :=
    IntrinsicArithmetic.GaloisValuationIntrinsic.lift_dilation_parameters E j ιE hj reps r d ε ωc ζc hζc hωc hrelc
  obtain ⟨e₀, e, he₀j, hej, hroot, he, hunit⟩ :=
    IntrinsicArithmetic.GaloisValuationIntrinsic.lift_dilation_root j ω M hM hω e₀c (SphericalActionModelInverse.parameterForConvention c e₀c)
      (by rw [hωj]; exact hrootc) hec
  have he0 : e ≠ 0 := by
    intro hz
    have hh := hunit 1
    simp [hz] at hh
  have hα' : SphericalActionModelInverse.ProjectivelyEqual (fun i => (α i : ℂ))
      (fun i => j (GaloisValuationCm.parameterTriple (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) e i)) := by
    convert hα using 1
    funext i
    fin_cases i <;> simp [GaloisValuationCm.parameterTriple, IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_image, hej]
  obtain ⟨β, hβ, hχβ, hconjβ⟩ := lift_actual_satake q hRationalStructure j
    (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) e (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_ne_zero q j) he0 χ α hχα hα'
  have hsplit (τ : Gal(E/ℚ)) : ν (ιE (τ (r : E))) =
      if τ = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0 := by
    dsimp [ν]
    rw [valuation_on_field, horders]
    split_ifs <;> simp
  have hnum := GaloisValuationCm.galois_sign_rule_for_parameter_valuations
    E ιE (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE) (IntrinsicArithmetic.GaloisValuationIntrinsic.restriction_commutes E ιE) v hv d hd reps hactive hpair
    q (Fact.out : q.Prime) M hM r hr ν
    (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_mul q _) (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_add q _) (IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation_q q _)
    hsplit e₀ e ω ζ ε hε hζ hrel hroot he j.toRatAlgHom hunit
    (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_sq q j) (fun σ i => σ (β i : IntrinsicArithmetic.GaloisValuationIntrinsic.Qbar))
    (projective_scalar_conjugate β (IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j) e hβ)
  refine ⟨ω, ζ, e₀, e, β, ?_, hζ, hrel, hroot, he, hβ, hχβ, hnum.1, ?_⟩
  · intro b
    rw [hωj]
    exact hθ' b
  · intro σ
    exact ⟨hconjβ σ, hnum.2 σ⟩

end

end OAI.RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic
