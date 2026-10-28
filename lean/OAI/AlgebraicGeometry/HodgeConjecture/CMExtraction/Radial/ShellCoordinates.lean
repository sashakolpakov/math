import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke

/-! # Shell Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.ShellCoordinates

noncomputable section

/-! Shell differences recover the actual ball-basis coordinates. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

theorem radialBasis_repr (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) (n : ℤ) :
    (Hecke.radialBasis q).repr b n = Hecke.shellCoefficient q n b := by
  have h : (Finsupp.lapply n).comp (Hecke.radialBasis q).repr.toLinearMap =
      Hecke.shellCoefficient q n := by
    apply (Hecke.radialBasis q).ext
    intro m
    change (Hecke.radialBasis q).repr (Hecke.radialBasis q m) n = Hecke.shellCoefficient q n (Hecke.radialBasis q m)
    rw [Module.Basis.repr_self, Hecke.radialBasis_apply, Hecke.shellCoefficient_ball]
    simp [Finsupp.single_apply, eq_comm]
  exact LinearMap.congr_fun h b

theorem radial_ext_sphere (b c : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q)
    (h : ∀ n, b.val (Hecke.spherePoint q n) = c.val (Hecke.spherePoint q n)) : b = c := by
  apply (Hecke.radialBasis q).repr.injective
  ext n
  rw [radialBasis_repr, radialBasis_repr]
  exact congrArg₂ (· - ·) (h n) (h (n - 1))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.ShellCoordinates
