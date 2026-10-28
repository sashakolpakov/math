import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Scalar
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Dilation

/-! # Auxiliary Dilation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.AuxiliaryDilation.CM

noncomputable section

/-! Construct RadialDilation's whole auxiliary family for the original source.
The fixed frame, finite radial action, determinant, Poisson relation,
algebraic scalars and exact Galois splitting are retained together. -/

open scoped Classical _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarFamily.CM.Family OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)

theorem exists_family
    (hLefschetzNormalization : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LefschetzNormalization.Proposition E)
    (hCotangentBundle : ∀ (B A : Type*) [CommSemiring B] [CommGroup A], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.CotangentBundle.Proposition B A _ _)
    (hCompletedTheta : ∀ (I : Type*) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _)
    (hNormOneApproximation : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.NormOneApproximation.Proposition) (hLocalWeil : RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.LocalWeil.Proposition)
    (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, 0, 0, 0})
    (hg : D.pel.HasIntegralModelGeometry) (hq : D.pel.IsGoodCompletelySplitPrime)
    (hb : D.pel.reference.b = B.b) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true) (hd : ∀ τ, d τ = v.val τ⁻¹) :
    ∃ u : MpF,
      FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D
        (ComplexAction.CM.Symplectic.frame E L.coordinates) u ∧
      ∀ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      ∃ hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1,
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        (ScalarFamily.CM.Family.halfDeterminant E L r hr * (r : ℂ)⁻¹) ^ 2 =
          ∏ τ ∈ Representatives.CM.representatives E places,
            ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
        ∃ ω ζ : ℂ, RepresentationTheory.Hecke.RadialDilation.Cm.finitePhase ζ ∧
          (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
            ScalarFamily.CM.Family.family E L (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ
              ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
            ω • ScalarFamily.CM.Family.family E L (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)) ∧
          ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
            ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
          RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle ω ∧
          (∀ e₀ : ℂ, e₀ ^ M = ω → RepresentationTheory.Hecke.RadialDilation.Cm.algebraicUnitCircle e₀) := by
  obtain ⟨u, hu, hfamily⟩ := SourceFinite.Scalar.CM.exists_inputs E L.coordinates D hb hLocalWeil hg hq ιE
  refine ⟨u, hu, ?_⟩
  intro φ hφ
  obtain ⟨r, M, hM, hr, hval, Uq, ξ, hJ, hξ, hUq, hf⟩ := hfamily φ hφ
  refine ⟨r, M, hM, hr, hval, ?_⟩
  exact Dilation.CM.relation E L hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy v hv hd r hr q M hM D.weil
    (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ) hJ Uq hUq ξ hξ hf

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.AuxiliaryDilation.CM
