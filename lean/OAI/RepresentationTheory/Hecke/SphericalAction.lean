import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricTheta
import OAI.RepresentationTheory.Hecke.RadialDilation.Mem

/-! # Spherical Action -/

namespace OAI.RepresentationTheory.Hecke.SphericalAction

noncomputable section

/-! Full prerequisite propositions. GeometricThetaInput is the previously audited
complete GeometricTheta proposition. RadialDilationInput reproduces every binder and conclusion
of the committed RadialDilation statement, with its reserved binder Σ renamed reps.
The radial functions below have the literal original definition. -/

open scoped Classical

abbrev GeometricThetaInput : Prop := AlgebraicGeometry.HodgeConjecture.CMExtraction.GeometricTheta.Intrinsic.GeometricThetaInput

def radialInput (q : ℕ) [Fact q.Prime] :
    Submodule ℂ ((Fin 3 → ℚ_[q]) → ℂ) :=
  Submodule.span ℂ
    (Set.range (fun j : ℤ => fun x : Fin 3 → ℚ_[q] =>
      if ∀ i, ‖x i‖ ≤ (q : ℝ) ^ (-j)
      then (1 : ℂ) else 0))

abbrev finitePhase := RadialDilation.Cm.finitePhase
abbrev algebraicUnitCircle := RadialDilation.Cm.algebraicUnitCircle

def RadialDilationInput : Prop := ∀
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hv : v.val 1 = true)
    (d : Gal(E/ℚ) → ℤ)
    (_hd : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (reps : Finset (Gal(E/ℚ)))
    (_hactive : (1 : Gal(E/ℚ)) ∈ reps)
    (_hrepresentatives : ∀ τ : Gal(E/ℚ),
      τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (r : Eˣ)
    (_hnorm : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (q : ℕ) [Fact q.Prime]
    (M : ℕ) (_hM : 0 < M)
    (S V : Type*)
    [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V]
    (j : radialInput q →ₗ[ℂ] S)
    (_hj : Function.Injective j)
    (Θ : S →ₗ[ℂ] V)
    (U : S →ₗ[ℂ] S)
    (D Uq : radialInput q →ₗ[ℂ] radialInput q)
    -- The prescribed normalization of D_q.
    (_hD : ∀ b x,
      (D b).val x =
        (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) *
          b.val (fun i => (q : ℚ_[q])⁻¹ * x i))
    -- Ordinary substitution for the local scalar of valuation M.
    (_hUq : ∀ b x,
      (Uq b).val x =
        (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
          b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i))
    (ξ : ℂ) (_hξ : finitePhase ξ)
    -- Includes the finite factors away from the active place.
    (_hfinite : ∀ b, U (j b) = ξ • j (Uq b))
    (halfDet : ℂ)
    -- Active determinant exponent 1 - 2; compact-place weights.
    (_hdet :
      halfDet ^ 2 =
        (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E)) ^ (1 - 2 : ℤ) *
          ∏ τ ∈ reps.erase 1,
            (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ))
    (ε : ℤ) (_hε : ε = 1 ∨ ε = -1)
    -- Bare projected-gradient covariance, before differential identification.
    (_hPoisson : ∀ f : S,
      Θ (U f) =
        ((halfDet *
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-ε)) •
            Θ f),
    -- Square of the bare archimedean scalar.
    (halfDet *
      (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ 2 =
        ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ)
    ∧
    ∃ ω ζ : ℂ,
      finitePhase ζ ∧
      -- Equivalently, Θ ∘ j factors through the relation D_q^M = ω.
      (∀ b : radialInput q,
        Θ (j ((D ^ M) b)) = ω • Θ (j b)) ∧
      ω ^ 2 =
        ζ * ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (ε * 3 * d τ) ∧
      algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ M = ω → algebraicUnitCircle e₀)

end

end OAI.RepresentationTheory.Hecke.SphericalAction
