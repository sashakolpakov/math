import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.NumberTheory.ArithmeticGroups.Levels

/-! # Torsion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Torsion.CM

noncomputable section

/-! Torsion freeness is derived from the actual full lattice and the integer
principal level. An actual principal uniformization then supplies the surface
record without an additional torsion-freeness premise. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {K : IntermediateField ℚ ℂ} [NumberField K] [NumberField.IsCMField K]

theorem ball_principal_torsion_free (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (hN : 3 ≤ N)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)
    (k : ℕ) (hk : 0 < k) (hpow : g ^ k = 1) : g = 1 := by
  exact NumberTheory.ArithmeticGroups.Levels.CongruenceLevel.principalLevel_torsion_free B.b B.lattice
    ⟨B.lattice_fg, B.lattice_full, B.lattice_stable⟩ N hN g
    ⟨hg.1, hg.2.2.1, hg.2.2.2⟩ k hk hpow

def principalSurfaceOfCover (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (hN : 3 ≤ N)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace)
    (hπ : B.IsBallCover N X π) : Cm.PrincipalBallSurface K B N where
  surface := ⟨X, hπ.1⟩
  torsion_free := ball_principal_torsion_free B N hN
  projection := π
  isBallCover := hπ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Torsion.CM
