import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineDescent
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SetupSurfaceFamily

/-! # Single Line Source Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineSourceFamily.CM

noncomputable section

/-! Construct the full HeckeCycles source family from actual descended forms,
with a single finite input and the original principal projection at all
positive multiples of one level. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

def SetupSourceRepresentatives {d : Gal(K/ℚ) → Bool}
    (L : HeckeCycles.GeometricSource.CM.LinePeriod K D.ball D.places d) (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places))
    (M : ℕ) (hDM : D.depth ∣ M)
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)) : Prop :=
  ∀ (N : ℕ) (hN : 0 < N) (hMN : M ∣ N),
    ∃ ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms
      (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).analyticModel (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).analyticSpace 1 0,
      CoverPullback.CM.ballCoverPullback K D.ball N (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
        (SetupSurfaceFamily.CM.setupSurfaceProjection K D N hN (hDM.trans hMN))
        (SetupSurfaceFamily.CM.setup_surface_projection_cover K D N hN (hDM.trans hMN)) 1 ω.val.val = BallForms.CM.sourceBallOneForm K L φ ∧
      HeckeCycles.GeometricSource.CM.RepresentsTheta K L φ (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
        (SetupSurfaceFamily.CM.setupSurfaceProjection K D N hN (hDM.trans hMN)) ω ∧
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).toOver) 1 (Θ N) =
        ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).deRhamBettiIso 1).hom
          ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).deRhamClass 1 ω.val)

variable (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K D.ball D.places (fun k τ => d k (D.places.representative τ)))
  (hμ : ∀ k, d k (D.places.representative D.places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K D.ball D.places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

include hμ hL

theorem exists_setup_single_source_family (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places)) :
    ∃ (M : ℕ) (_hM : 0 < M) (hDM : D.depth ∣ M)
      (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
      HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (d j) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) Θ ∧
      SetupSourceRepresentatives K D L φ M hDM Θ := by
  have hdesc := SingleLineDescent.CM.exists_single_source_descent_level K d Q hμ j L hL φ
  let M := D.depth * hdesc.choose
  have hM : 0 < M := Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 3) D.depth_ge_three) hdesc.choose_spec.1
  have hDM : D.depth ∣ M := dvd_mul_right _ _
  have hdata (N : ℕ) (hN : 0 < N) (hMN : M ∣ N) :
      ∃ θ : ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1),
        ∃ ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms
          (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).analyticModel (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).analyticSpace 1 0,
          CoverPullback.CM.ballCoverPullback K D.ball N (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
            (SetupSurfaceFamily.CM.setupSurfaceProjection K D N hN (hDM.trans hMN))
            (SetupSurfaceFamily.CM.setup_surface_projection_cover K D N hN (hDM.trans hMN)) 1 ω.val.val = BallForms.CM.sourceBallOneForm K L φ ∧
          HeckeCycles.GeometricSource.CM.RepresentsTheta K L φ (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
            (SetupSurfaceFamily.CM.setupSurfaceProjection K D N hN (hDM.trans hMN)) ω ∧
          ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).toOver) 1 θ =
            ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).deRhamBettiIso 1).hom
              ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).deRhamClass 1 ω.val) := by
    let π := SetupSurfaceFamily.CM.setupSurfaceProjection K D N hN (hDM.trans hMN)
    have hπ := SetupSurfaceFamily.CM.setup_surface_projection_cover K D N hN (hDM.trans hMN)
    have ha := hdesc.choose_spec.2 N ((dvd_mul_left hdesc.choose D.depth).trans hMN)
      (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) π hπ
    let ω := ha.choose
    let e := Albanese.HodgeComparisonIs.CM.Construction.bettiComplexificationEquiv (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) 1
    let c := ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).deRhamBettiIso 1).hom
      ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).deRhamClass 1 ω.val)
    exact ⟨e.symm c, ω, ha.choose_spec.1, ha.choose_spec.2, e.apply_symm_apply c⟩
  let Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1) :=
    fun N => if h : 0 < N ∧ M ∣ N then (hdata N h.1 h.2).choose else 0
  have hlevels (N : ℕ) (hN : 0 < N) (hMN : M ∣ N) := (hdata N hN hMN).choose_spec
  refine ⟨M, hM, hDM, Θ, ?_, ?_⟩
  · refine ⟨D.ball, D.places, L, φ, ?_⟩
    intro N hN hMN
    obtain ⟨ω, _, hrep, heq⟩ := hlevels N hN hMN
    refine ⟨SetupSurfaceFamily.CM.setupSurfaceProjection K D N hN (hDM.trans hMN),
      SetupSurfaceFamily.CM.setup_surface_projection_cover K D N hN (hDM.trans hMN), ω, hrep, ?_⟩
    simpa only [Θ, dite_eq_left (And.intro hN hMN)] using heq
  · intro N hN hMN
    simpa only [Θ, dite_eq_left (And.intro hN hMN)] using hlevels N hN hMN

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineSourceFamily.CM
