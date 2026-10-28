import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodInverse
import OAI.RepresentationTheory.Theta.Geometric.Rational.PeriodCM
import OAI.RepresentationTheory.Theta.Geometric.Period.Models
import OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny

/-! # Prescribed Rational Isogeny -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Actual prescribed denominator-cleared rational SU isogenies between the
constructed algebraic reference fibers, including CM equivariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

local instance Data.ActiveHeckeThetaData.prescribedClearedIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance Data.ActiveHeckeThetaData.prescribedClearedSmooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem Data.ActiveHeckeThetaData.exists_prescribed_rational_period_isogeny (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (g : D.RationalSU) (ha : D.away g ∈ D.awayLevel)
    (n : ℕ) (hn : ∀ v ∈ D.pel.reference.lattice,
      (q : ℤ) ^ n • D.rationalLinear g v ∈ D.pel.reference.lattice)
    (x : D.domain) (A : D.PeriodModel hg x) (B : D.PeriodModel hg (D.rationalPeriodPoint g x)) :
        ∃ F : A.abelian.toOver ⟶ B.abelian.toOver,
          IsMonHom F ∧ IsFinite F.left ∧ Etale F.left ∧ Surjective F.left ∧
          (∀ a, AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.abelian.toOver (A.action a) ≫ F =
            F ≫ AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap B.abelian.toOver (B.action a)) ∧
          ∀ t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map F (A.period t) =
            B.period (D.clearedPeriodTorusMap hg g n hn x t) := by
  have hai : D.away g⁻¹ ∈ D.awayLevel := by
    rw [map_inv]
    exact D.awayLevel.inv_mem ha
  obtain ⟨m, hm⟩ := D.away_level_clears_lattice hg hc g⁻¹ hai
  let y := D.rationalPeriodPoint g x
  let Φ := D.canonicalPeriodData hg x
  let Ψ := D.canonicalPeriodData hg y
  let f : Φ.space →ₗ[ℂ] Ψ.space := (q : ℤ) ^ n • D.rationalPeriodLinear g x
  let h : Ψ.space →ₗ[ℂ] Φ.space := (q : ℤ) ^ m • D.rationalPeriodLinear g⁻¹ y
  have hf : ∀ v, v ∈ Φ.periodIntegerLattice → f v ∈ Ψ.periodIntegerLattice :=
    D.cleared_rationalPeriodLinear_integral hg g n hn x
  have hh : ∀ v, v ∈ Ψ.periodIntegerLattice → h v ∈ Φ.periodIntegerLattice := by
    intro v hv
    have H := D.cleared_rationalPeriodLinear_integral hg g⁻¹ m hm y v hv
    change ((q : ℤ) ^ m • D.rationalPeriodLinear g⁻¹ y) v ∈
      D.periodLattice (D.periodMap g⁻¹ (D.periodMap g x.val)) at H
    rw [D.periodMap_inv_apply] at H
    exact H
  have hcomp : ∀ v, h (f v) = q ^ (n + m) • v := D.cleared_rationalPeriodLinear_complement hg g x n m
  have hcomp' : ∀ v, f (h v) = q ^ (n + m) • v := D.cleared_rationalPeriodLinear_right_complement hg g x n m
  have hN : 0 < q ^ (n + m) := pow_pos (Fact.out : q.Prime).pos _
  obtain ⟨F, hFg, hFfinite, hFetale, hFsurj, hF⟩ :=
    Torus.Isogeny.exists_algebraic_torus_isogeny Φ Ψ f h hf hh (q ^ (n + m)) hN hcomp hcomp'
      A.abelian B.abelian A.period B.period A.period_add B.period_add
  refine ⟨F, hFg, hFfinite, hFetale, hFsurj, ?_, hF⟩
  intro a
  exact D.algebraic_cleared_period_map_CM hg g n hn x A.abelian B.abelian A.period B.period
    A.action B.action A.period_action B.period_action F hF a

end

end OAI.RepresentationTheory.Theta.Geometric
