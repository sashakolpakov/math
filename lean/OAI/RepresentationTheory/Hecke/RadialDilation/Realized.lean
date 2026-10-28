import OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSpecs
import OAI.RepresentationTheory.Hecke.RadialDilation.RepresentativeEmbeddings

/-! # Realized -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Realized.Realization

noncomputable section

/-! Apply the unchanged RadialDilation theorem to the actual finite Weil and projected theta constructions. -/

open scoped Classical _root_.Matrix

def RadialDilationConclusion
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (reps : Finset Gal(E/ℚ)) (r : Eˣ) (q : ℕ) [Fact q.Prime] (M : ℕ) (d : Gal(E/ℚ) → ℤ)
    {S V : Type*} [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
    (Θ : S →ₗ[ℂ] V) (j : Cm.radialInput q →ₗ[ℂ] S) : Prop :=
  ∃ ω ζ : ℂ, Cm.finitePhase ζ ∧
    (∀ b : Cm.radialInput q, Θ (j ((Mem.Realization.dilation q ^ M) b)) = ω • Θ (j b)) ∧
    ω ^ 2 = ζ * ∏ τ ∈ reps, AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * d τ) ∧
    Cm.algebraicUnitCircle ω ∧
    (∀ e₀ : ℂ, e₀ ^ M = ω → Cm.algebraicUnitCircle e₀)

universe ur uf ua
variable {MpR : Type ur} {MpF : Type uf} {MpA : Type ua}
  [Group MpR] [Group MpF] [Group MpA]

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
variable (hLefschetzNormalization : Prerequisites.Core.LefschetzNormalization.Proposition E)
variable (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @Prerequisites.Core.CotangentBundle.Proposition B A _ _)
variable (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @Prerequisites.Core.Theta.Proposition I _ _)
variable (hNormOneApproximation : Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
variable (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition)
variable (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)) (hv : v.val 1 = true)
variable (reps : Finset Gal(E/ℚ)) (hactive : (1 : Gal(E/ℚ)) ∈ reps)
variable (hreps : ∀ τ : Gal(E/ℚ), τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
local instance c410RealizedDilation_repsDecidable : DecidableEq reps := Classical.decEq reps
variable (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
variable (q : ℕ) [Fact q.Prime] (M : ℕ) (hM : 0 < M)
variable (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex reps) MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex reps) ℚ) (s : MpF)
variable (Uq : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q) (ξ : ℂ)
variable (P Q : Matrix (FramePositivity.Realization.FrameIndex reps) (FramePositivity.Realization.FrameIndex reps) ℂ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex reps))
variable (hfinite : GeometricSpecs.Realization.FiniteRadialRealization q ⟨1, hactive⟩ D γ s Uq ξ M)
variable (htheta : GeometricSpecs.Realization.ThetaScalarRealization D γ ⟨1, hactive⟩ (fun τ => v.val τ.val⁻¹)
      (fun τ => RepresentativeEmbeddings.Realization.complexRepresentativeEmbeddings E reps τ (r : E)) P Q Z)

include hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hv hreps hr hM hfinite htheta in
theorem realized_algebraic_dilation_relation :
    RadialDilationConclusion E reps r q M (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
      (GeometricTheta.Realization.projectedFrameTheta ⟨1, hactive⟩ Q Z) (ConcreteFinite.Realization.coordinateRadialEmbedding q ⟨1, hactive⟩ D s) := by
  obtain ⟨hj, hξ, hUq, hf⟩ := hfinite
  obtain ⟨_, hdet, hPoisson⟩ := htheta
  have hd := RepresentativeEmbeddings.Realization.representative_halfDet_identity E reps hactive (fun τ => v.val τ⁻¹) r _ hdet
  have hp : ∀ f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex reps),
      GeometricTheta.Realization.projectedFrameTheta ⟨1, hactive⟩ Q Z (D.finiteAction γ f) =
        ((Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z * (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-(-1 : ℤ))) •
          GeometricTheta.Realization.projectedFrameTheta ⟨1, hactive⟩ Q Z f := by
    intro f
    simpa only [neg_neg, zpow_one, RepresentativeEmbeddings.Realization.complexRepresentativeEmbeddings] using hPoisson f
  have h := Cm.algebraic_dilation_relation E hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy v hv
    (fun τ => AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (fun _ => rfl) reps hactive hreps r hr q M hM
    (Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex reps)) (Fin 2 → ℂ)
    (ConcreteFinite.Realization.coordinateRadialEmbedding q ⟨1, hactive⟩ D s) hj (GeometricTheta.Realization.projectedFrameTheta ⟨1, hactive⟩ Q Z)
    (D.finiteAction γ).toLinearMap (Mem.Realization.dilation q) Uq (Mem.Realization.dilation_apply q) hUq ξ hξ hf
    (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z) hd (-1) (Or.inr rfl) hp
  exact h.2

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Realized.Realization
