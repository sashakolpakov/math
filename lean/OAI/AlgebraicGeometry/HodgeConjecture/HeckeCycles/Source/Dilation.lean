import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarWeights
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives
import OAI.RepresentationTheory.Hecke.RadialDilation.Cm
import OAI.RepresentationTheory.Hecke.RadialDilation.Mem

/-! # Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Dilation.CM

noncomputable section

/-! Apply full RadialDilation to the original source theta family. Its period,
Poisson covariance, determinant and representative set are all derived
from the source geometry; only the finite radial construction remains
an intermediate input here. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm OAI.RepresentationTheory.Hecke.RadialDilation.Mem.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarFamily.CM.Family OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem relation
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0,0,0,0})
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true) (hd : ∀ τ, d τ = v.val τ⁻¹)
    (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (q : ℕ) [Fact q.Prime] (M : ℕ) (hM : 0 < M)
    {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (J : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (hJ : Function.Injective J)
    (Uq : Module.End ℂ (RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q))
    (hUq : ∀ b x, (Uq b).val x =
      (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
        b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i))
    (ξ : ℂ) (hξ : RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ξ)
    (hfinite : ∀ b, W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) (J b) =
      ξ • J (Uq b)) :
    (ScalarFamily.CM.Family.halfDeterminant E L r hr * (r : ℂ)⁻¹) ^ 2 =
      ∏ τ ∈ Representatives.CM.representatives E places, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
    ∃ ω ζ : ℂ, RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ ∧
      (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q, ScalarFamily.CM.Family.family E L (J ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) = ω • ScalarFamily.CM.Family.family E L (J b)) ∧
      ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
      RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ M = ω → RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀) := by
  have hdet : ScalarFamily.CM.Family.halfDeterminant E L r hr ^ 2 =
      ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E) ^ (1 - 2 : ℤ) *
        ∏ τ ∈ (Representatives.CM.representatives E places).erase 1,
          ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) := by
    have h := ScalarWeights.CM.halfDet_square E r hr L 0
      (MultiplierSign.CM.zero_mem_domain E)
    change ScalarFamily.CM.Family.halfDeterminant E L r hr ^ 2 = (r : ℂ)⁻¹ *
      ∏ i ∈ Finset.univ.erase places.distinguished,
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (places.representative i) (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d (places.representative i))) at h
    have hp := Representatives.CM.product_erase E places
      (fun τ => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)))
    rw [hp] at h
    simpa only [show (1 - 2 : ℤ) = -1 from rfl, zpow_neg_one,
      ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply, AlgEquiv.one_apply] using h
  have hPoissonAutomorphy' : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.PoissonAutomorphy.Proposition.{0,0,0,0} :=
    fun _ _ _ _ _ _ _ _ _ W γ => hPoissonAutomorphy W γ
  have h := RepresentationTheory.Hecke.RadialDilation.Cm.algebraic_dilation_relation E hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy'
    v hv (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (d τ)) (fun τ => congrArg ComplexMultiplication.SignSwitch.CM.signValue (hd τ))
    (Representatives.CM.representatives E places) (Representatives.CM.active E places) (Representatives.CM.paired E places) r hr q M hM
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (B.Domain → GeometricSource.CM.BallChart →L[ℂ] ℂ) J hJ (ScalarFamily.CM.Family.family E L)
    (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr)).toLinearMap
    (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q) Uq (RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation_apply q) hUq ξ hξ hfinite (ScalarFamily.CM.Family.halfDeterminant E L r hr) hdet
    (-1) (Or.inr rfl) (by
      intro φ
      simp only [neg_neg, zpow_one, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply, AlgEquiv.one_apply]
      change ScalarFamily.CM.Family.family E L (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) =
        (ScalarFamily.CM.Family.halfDeterminant E L r hr * (r : ℂ)⁻¹) • ScalarFamily.CM.Family.family E L φ
      exact ScalarFamily.CM.Family.covariance E L r hr hPoissonAutomorphy W φ)
  simpa only [neg_one_mul, ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply, AlgEquiv.one_apply] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Dilation.CM
