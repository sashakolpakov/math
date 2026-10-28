import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.AlgebraicGeometry.HodgeConjecture.FundamentalComparison

/-! # Surface -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Surface.CM.Construction

noncomputable section

/-!
Consume the repaired ThetaCycle proposition as an explicit hypothesis, retaining its
balance, positive identity labels, and second-real-place requirement. Its
geometric complex fundamental-class pairing is proved equal to the rational
homology evaluation used by the SurfaceConstruction pushforward construction.
-/

open _root_.CategoryTheory

/-- Integral-to-rational homology commutes with the explicit degree transport. -/
theorem integralToRational_degreeCast (X : TopCat.{0}) {m n : ℕ} (h : m = n)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology m) :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n
      ((eqToHom (congrArg (fun k => (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology k) h)) z) =
      cast (congrArg (fun k => ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology k : Type)) h)
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X m z) := by
  cases h
  rfl

/-- The repaired ThetaCycle surface evaluation agrees with the canonical rational
fundamental class, rather than an arbitrary functional. -/
theorem surface_evaluate_eq_rational (S : ThetaCycle.Cm.ProjectiveSurface)
    (a : S.variety.complexCohomology 4) :
    S.evaluate a = ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace S.variety.toOver) 4 a
      (SurfaceConstructionQ.CM.fundamentalQInDegree S.variety 4 (by rw [S.property])) := by
  rw [ThetaCycle.Cm.ProjectiveSurface.evaluate_eq, FundamentalComparison.CM.SurfaceConstruction.projective_integralEvaluation]
  apply congrArg (fun z =>
    ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace S.variety.toOver) 4 a z)
  exact integralToRational_degreeCast (TopCat.of S.variety.analyticSpace)
    (show 2 * S.variety.complexDimension = 4 by rw [S.property])
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass S.variety.complexDimension S.variety.analyticSpace)

/-- Full repaired ThetaCycle, including arithmetic uniformization and deeper
principal covers. Only a consequence is used below; the input is not weakened. -/
def BallSurfaceSwitchInput (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] : Prop :=
  ∀ (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (_hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (_hid : ∀ i, (v i).val 1 = true)
    (_hother : ∃ τ : Gal(E/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (Nbase : ℕ) (_hNbase : 0 < Nbase),
    ∃ (B : HeckeCycles.GeometricSource.CM.BallDatum E) (N : ℕ) (S : ThetaCycle.Cm.PrincipalBallSurface E B N)
      (f : (i : Fin 4) → S.surface.variety.toOver ⟶ (R i).abelianVariety.toOver),
      0 < N ∧ Nbase ∣ N ∧
      S.surface.evaluate (ThetaCycle.Cm.fourClass E v R S.surface.variety f) ≠ 0 ∧
      ∀ L : ℕ, 0 < L →
        ∃ (M : ℕ) (T : ThetaCycle.Cm.PrincipalBallSurface E B M)
          (p : ThetaCycle.Cm.PrincipalRefinement E S T),
          0 < M ∧ L ∣ M ∧
          T.surface.evaluate
              (ThetaCycle.Cm.fourClass E v R T.surface.variety (fun i => p.map ≫ f i)) =
            (p.degree : ℂ) * S.surface.evaluate (ThetaCycle.Cm.fourClass E v R S.surface.variety f) ∧
          T.surface.evaluate
            (ThetaCycle.Cm.fourClass E v R T.surface.variety (fun i => p.map ≫ f i)) ≠ 0

/-- Extract precisely the geometric data used by the pushforward helpers. -/
theorem surface_exists_of_full_ThetaCycle (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hThetaCycle : BallSurfaceSwitchInput E)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hid : ∀ i, (v i).val 1 = true)
    (hother : ∃ τ : Gal(E/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i))) :
    ∃ (S : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (hS : S.complexDimension = 2)
      (f : (i : Fin 4) → S.toOver ⟶ (R i).abelianVariety.toOver),
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace S.toOver) 4
        (ThetaCycle.Cm.fourClass E v R S f) (SurfaceConstructionQ.CM.fundamentalQInDegree S 4 (by rw [hS])) ≠ 0 := by
  obtain ⟨B, N, S, f, _, _, hn, _⟩ := hThetaCycle v hbalance hid hother R 1 Nat.one_pos
  refine ⟨S.surface.variety, S.surface.property, f, ?_⟩
  rwa [surface_evaluate_eq_rational] at hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.Surface.CM.Construction
