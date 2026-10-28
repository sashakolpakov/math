import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuotientSheets
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCover

/-! # Principal Covers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalCovers.CM

noncomputable section

/-! Principal-level divisibility constructs the actual analytic quotient map.
Holomorphic local sheets, covering, and positive finite degree are derived.
For an algebraic representative of that quotient map, the accepted refinement
record follows with its canonical degree law proved by the existing helper. -/

open _root_.CategoryTheory
open scoped _root_.Manifold
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {K : IntermediateField ℚ ℂ} [NumberField K] [NumberField.IsCMField K]

theorem principal_level_mono (B : HeckeCycles.GeometricSource.CM.BallDatum K) {N M : ℕ} (hNM : N ∣ M)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel M g) : B.principalLevel N g := by
  obtain ⟨k, hk⟩ := hNM
  refine ⟨hg.1, hg.2.1, hg.2.2.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hg.2.2.2 x hx
  refine ⟨(k : ℤ) • y, B.lattice.smul_mem (k : ℤ) hy, ?_⟩
  rw [hxy, hk, Nat.cast_mul, mul_smul]

theorem principal_map_derived_cover_data
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N M : ℕ)
    (S : Cm.PrincipalBallSurface K B N) (T : Cm.PrincipalBallSurface K B M)
    (f : T.surface.variety.analyticSpace → S.surface.variety.analyticSpace)
    (hover : ∀ z : B.Domain, f (T.projection z) = S.projection z) :
    IsCoveringMap f ∧ Function.Surjective f ∧
      IsLocalDiffeomorph 𝓘(ℂ, T.surface.variety.analyticModel)
        𝓘(ℂ, S.surface.variety.analyticModel) 1 f ∧
      ∃ degree : ℕ, 0 < degree ∧
        ∀ x : S.surface.variety.analyticSpace,
          Nat.card {y : T.surface.variety.analyticSpace // f y = x} = degree := by
  have hlocal := QuotientSheets.CM.principal_map_local_diffeomorph B N M S T f hover
  have hcover : IsCoveringMap f := isLocalHomeomorph_iff_isCoveringMap.mp hlocal.isLocalHomeomorph
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨z, rfl⟩ := S.isBallCover.2.1 x
    exact ⟨T.projection z, hover z⟩
  let : PreconnectedSpace S.surface.variety.analyticSpace := BallConnected.CM.principal_quotient_preconnected B N S
  exact ⟨hcover, hsurj, hlocal, FiniteCover.CM.covering_positive_degree f hcover hsurj⟩

/-- Level divisibility supplies the analytic principal-quotient map and all
its local covering data; no map, local sheets, or degree are assumed. -/
theorem principal_analytic_refinement
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N M : ℕ)
    (S : Cm.PrincipalBallSurface K B N) (T : Cm.PrincipalBallSurface K B M)
    (hNM : N ∣ M) :
    ∃ f : T.surface.variety.analyticSpace → S.surface.variety.analyticSpace,
      (∀ z : B.Domain, f (T.projection z) = S.projection z) ∧
      IsCoveringMap f ∧ Function.Surjective f ∧
      IsLocalDiffeomorph 𝓘(ℂ, T.surface.variety.analyticModel)
        𝓘(ℂ, S.surface.variety.analyticModel) 1 f ∧
      ∃ degree : ℕ, 0 < degree ∧
        ∀ x : S.surface.variety.analyticSpace,
          Nat.card {y : T.surface.variety.analyticSpace // f y = x} = degree := by
  have hfibers : ∀ z w : B.Domain, T.projection z = T.projection w → S.projection z = S.projection w := by
    intro z w hzw
    obtain ⟨g, hg, hact⟩ := (T.isBallCover.2.2.2.2.2 z w).mp hzw
    exact (S.isBallCover.2.2.2.2.2 z w).mpr ⟨g, principal_level_mono B hNM g hg, hact⟩
  let f := HeckeCycles.CoverFactor.CM.factor T.projection S.projection T.isBallCover.2.1
  have hover : ∀ z : B.Domain, f (T.projection z) = S.projection z :=
    HeckeCycles.CoverFactor.CM.factor_comp T.projection S.projection T.isBallCover.2.1 hfibers
  exact ⟨f, hover, principal_map_derived_cover_data B N M S T f hover⟩

/-- An actual algebraic principal quotient map produces the accepted
refinement, with local sheets and its finite positive degree derived. -/
theorem refinement_of_principal_algebraic_map
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N M : ℕ)
    (S : Cm.PrincipalBallSurface K B N) (T : Cm.PrincipalBallSurface K B M)
    (hNM : N ∣ M)
    (f : T.surface.variety.toOver ⟶ S.surface.variety.toOver)
    (hover : ∀ z : B.Domain,
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (T.projection z) = S.projection z) :
    ∃ p : Cm.PrincipalRefinement K S T, p.map = f := by
  obtain ⟨hcover, hsurj, hlocal, degree, hpos, hdegree⟩ :=
    principal_map_derived_cover_data B N M S T
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) hover
  exact ⟨Cover.CM.refinementOfHolomorphicCover K S T hNM f hover hcover degree hpos hdegree hlocal, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalCovers.CM
