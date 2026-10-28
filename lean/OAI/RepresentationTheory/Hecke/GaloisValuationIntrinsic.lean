import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse
import OAI.RepresentationTheory.Satake.RationalStructure

/-! # Galois Valuation Intrinsic -/

namespace OAI.RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic

noncomputable section

/-! Complete prerequisite propositions, copied as types only. No statement stub is imported.
The reserved source identifier Σ is spelled reps. -/

open scoped Classical TensorProduct

namespace LefschetzNormalization
variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

abbrev G := Gal(E/ℚ)

-- `true` denotes +1; `false` denotes -1.
abbrev Sign := AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
  (fun τ : G E => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)

abbrev FourTypes := Fin 4 → Sign E

-- Slots 0,1 are the manuscript's first two factors.
def switchLabels : Fin 4 → G E :=
  fun i => if i.val < 2 then 1 else AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E

def embeddingGenerator (τ : G E) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E :=
  AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)

def Proposition : Prop := ∀
    (s : ℕ)
    (_hdegree : Fintype.card (G E) = 2 * s)
    (A₂ : Sign E → Sign E → G E → G E → Prop)
    (A₄ : FourTypes E → (Fin 4 → G E) → Prop)
    (_h11 :
      ∀ (u v : Sign E) (a b : G E),
        (∀ σ : G E,
          AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (u.val (σ * a)) +
            AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (σ * b)) = 0) →
        A₂ u v a b)
    (_hproduct :
      ∀ (v : FourTypes E) (a : Fin 4 → G E)
        (p : Equiv.Perm (Fin 4)),
        A₂ (v (p 0)) (v (p 1)) (a (p 0)) (a (p 1)) →
        A₂ (v (p 2)) (v (p 3)) (a (p 2)) (a (p 3)) →
        A₄ v a)
    (_hscalar :
      ∀ (v : FourTypes E) (a : Fin 4 → G E) (g : G E),
        A₄ v (fun i => g * a i) ↔ A₄ v a)
    (_htransfer :
      ∀ (u v : FourTypes E) (a b : Fin 4 → G E)
        (f : Fin 4 → (E →ₗ[ℚ] E)),
        (∀ i,
          AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (u i))
            (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (f i)) →
        (∀ i,
          (f i).baseChange ℂ (embeddingGenerator E (a i)) =
            embeddingGenerator E (b i)) →
        A₄ u a → A₄ v b)
    (v : FourTypes E)
    (_hbalance :
      ∀ τ : G E,
        AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
          AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)),
    -- No common positive coordinate: two opposite pairs suffice.
    ((¬ ∃ g : G E,
        (v 0).val g = true ∧ (v 1).val g = true) ∧
      (∀ τ : G E,
        (v 1).val τ = !((v 0).val τ) ∧
        (v 3).val τ = !((v 2).val τ)) ∧
      A₄ v (switchLabels E))
    ∨
    -- Otherwise normalize a common positive coordinate to the identity.
    (∃ (g : G E) (w : FourTypes E)
        (d : Fin 4 → G E → Bool) (reps : Finset (G E)),
      (∀ i σ, (w i).val σ = (v i).val (σ * g)) ∧
      (∀ i, (w i).val 1 = true) ∧
      (∀ τ : G E,
        AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val τ) =
          AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val τ) + AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val τ)) ∧
      -- These actual rational maps implement the line transfer.
      (∀ i,
        AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i))
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)) (g⁻¹).toLinearMap) ∧
      (∀ τ : G E,
        (g⁻¹).toLinearMap.baseChange ℂ (embeddingGenerator E τ) =
          embeddingGenerator E (τ * g)) ∧
      (∀ i τ, d i τ = (w i).val τ⁻¹) ∧
      (∀ i τ, d i (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = !(d i τ)) ∧
      (1 : G E) ∈ reps ∧
      (∀ τ : G E,
        τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) ∧
      reps.card = s ∧
      (A₄ w (switchLabels E) ↔ A₄ v (switchLabels E)) ∧
      ((s = 1 ∧ A₄ v (switchLabels E)) ∨ 2 ≤ s))
end LefschetzNormalization

namespace RadialDilation
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
def Proposition : Prop := ∀
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
    (j : RadialDilation.Cm.radialInput q →ₗ[ℂ] S)
    (_hj : Function.Injective j)
    (Θ : S →ₗ[ℂ] V)
    (U : S →ₗ[ℂ] S)
    (D Uq : RadialDilation.Cm.radialInput q →ₗ[ℂ] RadialDilation.Cm.radialInput q)
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
    (ξ : ℂ) (_hξ : RadialDilation.Cm.finitePhase ξ)
    -- Includes the finite factors away from the active place.
    (_hfinite : ∀ b, U (j b) = ξ • j (Uq b))
    (_halfDet : ℂ)
    -- Active determinant exponent 1 - 2; compact-place weights.
    (_hdet :
      _halfDet ^ 2 =
        (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E)) ^ (1 - 2 : ℤ) *
          ∏ τ ∈ reps.erase 1,
            (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ))
    (ε : ℤ) (_hε : ε = 1 ∨ ε = -1)
    -- Bare projected-gradient covariance, before differential identification.
    (_hPoisson : ∀ f : S,
      Θ (U f) =
        ((_halfDet *
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-ε)) •
            Θ f),
    -- Square of the bare archimedean scalar.
    (_halfDet *
      (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ 2 =
        ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ)
    ∧
    ∃ ω ζ : ℂ,
      RadialDilation.Cm.finitePhase ζ ∧
      -- Equivalently, Θ ∘ j factors through the relation D_q^M = ω.
      (∀ b : RadialDilation.Cm.radialInput q,
        Θ (j ((D ^ M) b)) = ω • Θ (j b)) ∧
      ω ^ 2 =
        ζ * ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (ε * 3 * d τ) ∧
      RadialDilation.Cm.algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ M = ω → RadialDilation.Cm.algebraicUnitCircle e₀)
end RadialDilation

namespace SphericalAction
open OAI.RepresentationTheory.Hecke.SphericalActionModelInverse
def Proposition : Prop := ∀
    (q : ℕ) [Fact q.Prime] (c : SphericalActionModelInverse.ActingConvention)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (ρV : SphericalActionModelInverse.SphericalAlgebra q →ₐ[ℂ] Module.End ℂ V)
    (Θ : SphericalActionModelInverse.Radial q →ₗ[ℂ] V)
    (M : ℕ) (_hM : 0 < M) (ω : ℂ) (_hω : ‖ω‖ = 1)
    (_hC48 : ∀ h b, Θ (SphericalActionModelInverse.radialAction q c h b) = ρV h (Θ b))
    (_hC410 : ∀ b, Θ ((AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) b) = ω • Θ b),
    SphericalActionModelInverse.RadialSatakeConclusion q c ρV Θ M ω
end SphericalAction

namespace RationalStructure
open OAI.RepresentationTheory.Satake.RationalStructure.Construction
def Proposition : Prop := ∀
    (s : ℕ)
    (L : AddSubgroup (Satake.RationalStructure.Construction.AmbientCocharacters s))
    (D : Type*)
    (q : ℕ) (_hq : q.Prime)
    (a : D → L → ℚ)
    (S : (D →₀ ℂ) →ₗ[ℂ] (L →₀ ℂ))
    (_hformula : ∀ d l,
      S (Finsupp.single d 1) l =
        (q : ℂ) ^ Satake.RationalStructure.Construction.rhoPairing l * (a d l : ℂ)),
    -- Descent to rational Hecke coefficients.
    (∃ SQ : (D →₀ ℚ) →ₗ[ℚ] (L →₀ ℚ),
      ∀ f, Satake.RationalStructure.Construction.extendQ (SQ f) = S (Satake.RationalStructure.Construction.extendQ f)) ∧
    -- Scalar conjugation commutes with normalized Satake.
    (∀ (σ : ℂ ≃ₐ[ℚ] ℂ) (f : D →₀ ℂ),
      S (Satake.RationalStructure.Construction.conjugateCoefficients σ f) =
        Satake.RationalStructure.Construction.conjugateCoefficients σ (S f)) ∧
    -- Conjugated eigenvalues have the conjugated torus parameter.
    (∀ (σ : ℂ ≃ₐ[ℚ] ℂ) (χ : D → ℂ) (z : L → ℂ),
      Satake.RationalStructure.Construction.IsSatakeParameter S χ z →
        Satake.RationalStructure.Construction.IsSatakeParameter S
          (fun d => σ (χ d))
          (fun l => σ (z l)))
end RationalStructure

end

end OAI.RepresentationTheory.Hecke.GaloisValuationIntrinsic.Intrinsic
