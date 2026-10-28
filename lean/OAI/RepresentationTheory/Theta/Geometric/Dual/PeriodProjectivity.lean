import OAI.RepresentationTheory.Theta.Geometric.Dual.PeriodHermitian
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Period Projectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Projectivity of the torus formed with the actual integral dual lattice. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

instance Data.ActiveHeckeThetaData.dualPeriodTorus_compact (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    CompactSpace ((D.canonicalPeriodData hg x).space ⧸ (D.periodDualLattice hg x).toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic (D.periodDualLattice hg x)
    (QuotientAddGroup.mk : (D.canonicalPeriodData hg x).space →
      (D.canonicalPeriodData hg x).space ⧸ (D.periodDualLattice hg x).toAddSubgroup)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

theorem Data.ActiveHeckeThetaData.dualPeriod_projective (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus (D.canonicalPeriodData hg x).space
      (D.periodDualLattice hg x).toAddSubgroup := by
  let : DiscreteTopology (D.periodDualLattice hg x).toAddSubgroup :=
    D.periodDualLattice_discrete hg x
  exact (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (D.canonicalPeriodData hg x).space
    (D.periodDualLattice hg x).toAddSubgroup).mpr (D.dualPeriod_positive_integral hg x)

def Data.ActiveHeckeThetaData.dualCanonicalPeriodData (hg : D.pel.HasIntegralModelGeometry) (x : D.domain) :
    Torus.Data.CM.ProjectivePeriodData where
  space := (D.canonicalPeriodData hg x).space
  periodIntegerLattice := D.periodDualLattice hg x
  periodIntegerLattice_discrete := D.periodDualLattice_discrete hg x
  periodIntegerLattice_full := D.periodDualLattice_full hg x
  projective := D.dualPeriod_projective hg x

end

/-! A normalized holomorphic Poincare factor on the product of the
original period space with its integral dual lattice. -/

section

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def Dual.PeriodProjectivity.poincareAutomorphy (l m w z : V) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (H l z + H m w + H l m))

theorem Dual.PeriodProjectivity.poincareAutomorphy_ne_zero (l m w z : V) : Dual.PeriodProjectivity.poincareAutomorphy H l m w z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem Dual.PeriodProjectivity.poincareAutomorphy_zero (w z : V) : Dual.PeriodProjectivity.poincareAutomorphy H 0 0 w z = 1 := by
  simp [Dual.PeriodProjectivity.poincareAutomorphy]

@[simp] theorem Dual.PeriodProjectivity.poincareAutomorphy_abelian_zero (l w : V) : Dual.PeriodProjectivity.poincareAutomorphy H l 0 w 0 = 1 := by
  simp [Dual.PeriodProjectivity.poincareAutomorphy]

@[simp] theorem Dual.PeriodProjectivity.poincareAutomorphy_dual_zero (m z : V) : Dual.PeriodProjectivity.poincareAutomorphy H 0 m 0 z = 1 := by
  simp [Dual.PeriodProjectivity.poincareAutomorphy]

theorem Dual.PeriodProjectivity.poincareAutomorphy_add (hsym : ∀ u v, H v u = star (H u v))
    (l l' m m' w z : V) (hint : ∃ n : ℤ, (H l' m).im = (n : ℝ)) :
    Dual.PeriodProjectivity.poincareAutomorphy H (l + l') (m + m') w z =
      Dual.PeriodProjectivity.poincareAutomorphy H l m (w + l') (z + m') * Dual.PeriodProjectivity.poincareAutomorphy H l' m' w z := by
  obtain ⟨n, hn⟩ := hint
  have hs := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.hermitian_skew H hsym l' m
  rw [hn] at hs
  push_cast at hs
  simp only [Dual.PeriodProjectivity.poincareAutomorphy, map_add, LinearMap.add_apply]
  rw [← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨n, ?_⟩
  linear_combination (Real.pi : ℂ) * hs

theorem Dual.PeriodProjectivity.poincareAutomorphy_differentiable [FiniteDimensional ℂ V] (l m : V) :
    Differentiable ℂ (fun p : V × V => Dual.PeriodProjectivity.poincareAutomorphy H l m p.1 p.2) := by
  exact (((((H l).toContinuousLinearMap.differentiable.comp differentiable_snd).add
    ((H m).toContinuousLinearMap.differentiable.comp differentiable_fst)).add_const _).const_mul _).cexp

end

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.periodPoincareAutomorphy_add (hg : D.pel.HasIntegralModelGeometry) (x : D.domain)
    (l l' : D.periodDualLattice hg x)
    (m m' : (D.canonicalPeriodData hg x).periodIntegerLattice)
    (w z : (D.canonicalPeriodData hg x).space) :
    Dual.PeriodProjectivity.poincareAutomorphy (D.periodHermitian hg x) (l.val + l'.val) (m.val + m'.val) w z =
      Dual.PeriodProjectivity.poincareAutomorphy (D.periodHermitian hg x) l.val m.val (w + l'.val) (z + m'.val) *
        Dual.PeriodProjectivity.poincareAutomorphy (D.periodHermitian hg x) l'.val m'.val w z := by
  apply Dual.PeriodProjectivity.poincareAutomorphy_add _ (D.periodHermitian_hermitian hg x)
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp (l'.property m.val m.property)
  exact ⟨n, hn.symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric
