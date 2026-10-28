import OAI.RepresentationTheory.Hecke.RadialDilation.Mem

/-! # Intrinsic Dilation -/

namespace OAI.NumberTheory.PadicHodge.IntrinsicDilation.FrobeniusSlopeIntrinsic

noncomputable section

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.Mem.Realization

/-- Full unchanged RadialDilation proposition on its concrete radial space. -/
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
    (j : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] S)
    (_hj : Function.Injective j)
    (Θ : S →ₗ[ℂ] V)
    (U : S →ₗ[ℂ] S)
    (D Uq : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
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
    (ξ : ℂ) (_hξ : RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ξ)
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
      RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ ∧
      -- Equivalently, Θ ∘ j factors through the relation D_q^M = ω.
      (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
        Θ (j ((D ^ M) b)) = ω • Θ (j b)) ∧
      ω ^ 2 =
        ζ * ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (ε * 3 * d τ) ∧
      RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ M = ω → RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀)

/-- Natural RadialDilation premises. The radial theta map is the actual composition
of the supplied insertion and projected theta map. Dilation is canonical. -/
structure DilationData (q : ℕ) [Fact q.Prime]
    (V : Type) [AddCommGroup V] [Module ℂ V] where
  E : IntermediateField ℚ ℂ
  [numberField : NumberField E]
  [galois : IsGalois ℚ E]
  [cm : NumberField.IsCMField E]
  v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)
  hv : v.val 1 = true
  d : Gal(E/ℚ) → ℤ
  hd : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)
  reps : Finset Gal(E/ℚ)
  hactive : (1 : Gal(E/ℚ)) ∈ reps
  hreps : ∀ τ : Gal(E/ℚ), τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps
  unit : Eˣ
  hunit : (unit : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (unit : E) = 1
  M : ℕ
  hM : 0 < M
  S : Type
  [addS : AddCommGroup S]
  [moduleS : Module ℂ S]
  insertion : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] S
  hinsertion : Function.Injective insertion
  theta : S →ₗ[ℂ] V
  U : S →ₗ[ℂ] S
  Uq : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q
  hUq : ∀ b x, (Uq b).val x =
    (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
      b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)
  ξ : ℂ
  hξ : RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ξ
  hfinite : ∀ b, U (insertion b) = ξ • insertion (Uq b)
  halfDet : ℂ
  hdet : halfDet ^ 2 =
    (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (unit : E)) ^ (1 - 2 : ℤ) *
      ∏ τ ∈ reps.erase 1, (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (unit : E)) ^ (-3 * d τ)
  hPoisson : ∀ f : S, theta (U f) =
    ((halfDet * (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (unit : E))⁻¹) ^ (-(-1 : ℤ))) • theta f

attribute [instance] DilationData.numberField DilationData.galois DilationData.cm
  DilationData.addS DilationData.moduleS

namespace DilationData
variable {q : ℕ} [Fact q.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]

def radialTheta (B : DilationData q V) : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] V := B.theta.comp B.insertion

theorem full_dilation (B : DilationData q V) (hRadialDilation : RadialDilationInput.{0, 0}) :
    (B.halfDet * (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv B.E 1 (B.unit : B.E))⁻¹) ^ 2 =
      ∏ τ ∈ B.reps, (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv B.E τ (B.unit : B.E)) ^ (-3 * B.d τ) ∧
    ∃ ω ζ : ℂ, RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ ∧
      (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q, B.radialTheta ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ B.M) b) = ω • B.radialTheta b) ∧
      ω ^ 2 = ζ * ∏ τ ∈ B.reps,
        (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv B.E τ (B.unit : B.E)) ^ (-3 * B.d τ) ∧
      RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ B.M = ω → RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀) := by
  have h := hRadialDilation B.E B.v B.hv B.d B.hd B.reps B.hactive B.hreps B.unit B.hunit
    q B.M B.hM B.S V B.insertion B.hinsertion B.theta B.U (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) B.Uq
    (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation_apply q) B.hUq B.ξ B.hξ B.hfinite B.halfDet B.hdet (-1) (Or.inr rfl) B.hPoisson
  simpa only [DilationData.radialTheta, LinearMap.comp_apply, neg_one_mul] using h

end DilationData

end

end OAI.NumberTheory.PadicHodge.IntrinsicDilation.FrobeniusSlopeIntrinsic
