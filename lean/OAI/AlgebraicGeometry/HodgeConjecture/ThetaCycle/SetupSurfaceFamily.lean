import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HeckeCycles

/-! # Setup Surface Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SetupSurfaceFamily.CM

noncomputable section

/-! The actual principal surfaces form a total family for HeckeCycles. At every
positive level divisible by the setup depth this is exactly the original
surface; other indices use the surface at the setup depth. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

def setupSurfaceFamily (N : ℕ) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  if h : 0 < N ∧ D.depth ∣ N then (D.surface N h.1 h.2).surface.variety
  else (D.surface D.depth (lt_of_lt_of_le (by decide : 0 < 3) D.depth_ge_three) dvd_rfl).surface.variety

theorem setup_surface_family_eq (N : ℕ) (hN : 0 < N) (hD : D.depth ∣ N) :
    setupSurfaceFamily K D N = (D.surface N hN hD).surface.variety := by
  simp only [setupSurfaceFamily, dite_eq_left (And.intro hN hD)]

def setupSurfaceProjection (N : ℕ) (hN : 0 < N) (hD : D.depth ∣ N) :
    D.ball.Domain → (setupSurfaceFamily K D N).analyticSpace :=
  (setup_surface_family_eq K D N hN hD).symm ▸ (D.surface N hN hD).projection

omit D [IsGalois ℚ K] in
theorem source_cover_transport {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N : ℕ} {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (h : X = Y) (π : B.Domain → Y.analyticSpace) (hπ : B.IsBallCover N Y π) :
    B.IsBallCover N X (h.symm ▸ π) := by
  cases h
  exact hπ

theorem setup_surface_projection_cover (N : ℕ) (hN : 0 < N) (hD : D.depth ∣ N) :
    D.ball.IsBallCover N (setupSurfaceFamily K D N) (setupSurfaceProjection K D N hN hD) :=
  source_cover_transport K (setup_surface_family_eq K D N hN hD)
    (D.surface N hN hD).projection (D.surface N hN hD).isBallCover

theorem setup_surface_family_cover (N : ℕ) (hN : 0 < N) (hD : D.depth ∣ N) :
    ∃ π : D.ball.Domain → (setupSurfaceFamily K D N).analyticSpace,
      D.ball.IsBallCover N (setupSurfaceFamily K D N) π :=
  ⟨setupSurfaceProjection K D N hN hD, setup_surface_projection_cover K D N hN hD⟩

def setupSurfaceHodge (N : ℕ) : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((setupSurfaceFamily K D N).rationalCohomology 1) :=
  Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 (setupSurfaceFamily K D N)

theorem setup_surface_hodge_canonical (N : ℕ) :
    Albanese.HodgeComparisonIs.CM.Construction.IsCanonicalH1 (setupSurfaceFamily K D N) (setupSurfaceHodge K D N) :=
  Albanese.HodgeComparisonIs.CM.Construction.canonicalH1_isCanonical _

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SetupSurfaceFamily.CM
