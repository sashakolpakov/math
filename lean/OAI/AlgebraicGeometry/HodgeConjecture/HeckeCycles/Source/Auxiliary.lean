import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.AuxiliaryDilation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters
import OAI.RepresentationTheory.Hecke.GaloisValuationCm

/-! # Auxiliary -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary.CM

/-! Lift the original source family's dilation scalar through the same
algebraic-closure embedding used by the Hecke characters. The complete
splitting formula and all conjugate norms remain attached to that scalar. -/

open scoped Classical _root_.Matrix BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices
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
    (hb : D.pel.reference.b = B.b)
    (j : CMExtraction.ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true) (hd : ∀ τ, d τ = v.val τ⁻¹) :
    ∃ u : MpF,
      FixedFrameAuxiliaryFamily.CM.Family.CoordinateIdentity E D
        (ComplexAction.CM.Symplectic.frame E L.coordinates) u ∧
      ∀ φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished), φ ≠ 0 →
      ∃ (r : Eˣ) (M : ℕ) (ω ζ : CMExtraction.ParameterChoices.Qbar),
        0 < M ∧ (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1 ∧
        (∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
          (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D.pel ιE (D.pel.reference.distinguished, false)) (ιE (τ (r : E))) =
            if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0) ∧
        (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧
        ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
          (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
        (∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ ω)‖ = 1) ∧
        (∀ e₀ : CMExtraction.ParameterChoices.Qbar, e₀ ^ M = ω → ∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j (σ e₀)‖ = 1) ∧
        (∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q,
          ScalarFamily.CM.Family.family E L (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ
            ((RepresentationTheory.Hecke.RadialDilation.Mem.Realization.dilation q ^ M) b)) =
          j ω • ScalarFamily.CM.Family.family E L (CMExtraction.AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b)) := by
  obtain ⟨u, hu, hf⟩ := AuxiliaryDilation.CM.exists_family E L D
    hLefschetzNormalization hCotangentBundle hCompletedTheta hNormOneApproximation hLocalWeil hPoissonAutomorphy hg hq hb ιE v hv hd
  refine ⟨u, hu, ?_⟩
  intro φ hφ
  obtain ⟨r, M, hM, hr, hval, _hsq, ωc, ζc, hζc, hfamily, hrel, hωc, _hroot⟩ := hf φ hφ
  obtain ⟨ω, ζ, hωj, _hζj, hζ, hω, hnorm⟩ := CMExtraction.Parameters.ParameterChoices.lift_dilation_parameters E j ιE hι
    (Representatives.CM.representatives E places) r (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (d τ)) (-1) ωc ζc hζc hωc
    (by simpa only [neg_one_mul] using hrel)
  refine ⟨r, M, ω, ζ, hM, hr, hval, hζ, ?_, hnorm, ?_, ?_⟩
  · simpa only [neg_one_mul] using hω
  · intro e₀ he₀
    exact CMExtraction.Parameters.ParameterChoices.root_all_conjugates_norm_one j ω e₀ M hM he₀ hnorm
  · simpa only [hωj] using hfamily

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary.CM.RootValuations

/-! The original source's dilation identity determines every Galois
valuation of its roots. Its own representative set is used throughout. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Parameters.ParameterChoices
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (places : GeometricSource.CM.Places E)
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
  (r : Eˣ) (M : ℕ) (hM : 0 < M)
  (hsplit : ∀ τ : Gal(E/ℚ), NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q
    (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (ιE (τ (r : E))) =
      if τ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E then (M : ℚ) else if τ = 1 then -(M : ℚ) else 0)
  (ω ζ : CMExtraction.ParameterChoices.Qbar) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1)
  (hrel : ω ^ 2 = ζ * ∏ τ ∈ Representatives.CM.representatives E places,
    (ιE (τ (r : E))) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)))
  (a : CMExtraction.ParameterChoices.Qbarˣ) (ha : (a : CMExtraction.ParameterChoices.Qbar) ^ M = ω)

include hM hsplit hζ hrel ha in
theorem conjugate_valuation (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ (a : CMExtraction.ParameterChoices.Qbar)) =
      (3 / 2 : ℚ) * ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) := by
  have h := RepresentationTheory.Hecke.GaloisValuationCm.dilation_root_valuation ιE (CMExtraction.ParameterChoices.restriction E ιE) (CMExtraction.ParameterChoices.restriction_commutes E ιE)
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_ne_one E) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E)
    (fun τ => ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) (RepresentationTheory.Hecke.GaloisValuationCm.inverse_sign_odd E v _ (fun _ => rfl))
    (Representatives.CM.representatives E places) (Representatives.CM.paired E places)
    r M hM (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)))
    (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) hsplit (a : CMExtraction.ParameterChoices.Qbar) ω ζ a.ne_zero (-1) hζ
    (by simpa only [neg_one_mul] using hrel) ha σ
  simpa only [Int.cast_neg, Int.cast_one, neg_neg, one_mul, inv_inv] using h

include hM hsplit hζ hrel ha in
theorem base_valuation (hv : v.val 1 = true) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (a : CMExtraction.ParameterChoices.Qbar) =
      (3 / 2 : ℚ) := by
  simpa [hv, ComplexMultiplication.SignSwitch.CM.signValue] using conjugate_valuation E places D ιE v r M hM hsplit ω ζ hζ hrel a ha 1

include hM hsplit hζ hrel ha in
theorem inverse_conjugate_valuation (σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ)) :
    NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation q (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ ((a : CMExtraction.ParameterChoices.Qbar)⁻¹)) =
      (-3 / 2 : ℚ) * ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) := by
  rw [map_inv₀, RepresentationTheory.Hecke.GaloisValuationCm.val_inv _ (NumberTheory.PadicHodge.Arithmetic.CM.ExtremeSlopesAdapter.globalValuation_mul q _) _ ((map_ne_zero σ).mpr a.ne_zero),
    conjugate_valuation E places D ιE v r M hM hsplit ω ζ hζ hrel a ha σ]
  ring

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary.CM.RootValuations

end

end OAI
