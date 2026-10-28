import OAI.RepresentationTheory.Theta.Geometric.OddSections
import OAI.RepresentationTheory.Theta.Geometric.QuadraticSections

/-! # Consecutive Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.ConsecutiveSections.CM.Torus.ProjectivePeriodData

noncomputable section

/-! Consecutive powers of the original polarization have holomorphic generators. -/

open scoped ContDiff

open OAI.RepresentationTheory.Theta.Geometric.QuadraticSections.RiemannProjectivityConstruction

variable (Φ : Torus.Data.CM.ProjectivePeriodData)

local instance : DecidableEq (Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup) := Classical.decEq _

def _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.AutomorphyFactor.GeneratedPower (J : Φ.AutomorphyFactor) (n : ℕ) : Prop :=
  ∀ p : Φ.space, ∃ t : Φ.space → ℂ, ContDiff ℂ ∞ t ∧ t p ≠ 0 ∧
    ∀ (l : Φ.periodIntegerLattice) z, t (z + l.val) = J.value l z ^ n * t z

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.interpolation_generated_power
    (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (J : Φ.AutomorphyFactor) (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))
    (hdouble : ∀ l : Φ.periodIntegerLattice, l ∈ Φ.doubleSubgroup → ∀ z,
      J.value l z = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (Φ.halfHermitian H) l.val z)
    (F : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.FiniteSectionFamily (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup)
    (hFi : Function.Injective F.projectiveMap) (k : ℕ)
    (hbg : ∀ p, ∃ t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup k, t p ≠ 0) :
    J.GeneratedPower Φ
      (F.degree * Fintype.card {c : Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup // c ≠ 0} * 2 + k) := by
  classical
  let C := Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup
  let I := {c : C // c ≠ 0}
  let r (c : C) : Φ.periodIntegerLattice := Quotient.out c
  have hr (c : C) : (QuotientAddGroup.mk (r c) : C) = c := Quotient.out_eq c
  let n := F.degree * Fintype.card I * 2 + k
  intro p
  have hneq (c : I) :
      (QuotientAddGroup.mk p : Φ.space ⧸ Φ.doubledLattice.toAddSubgroup) ≠
        QuotientAddGroup.mk (p + (r c.val).val) := by
    intro he
    have hz : (QuotientAddGroup.mk (r c.val).val : Φ.space ⧸ Φ.doubledLattice.toAddSubgroup) = 0 := by
      apply add_left_cancel (a := (QuotientAddGroup.mk p : Φ.space ⧸ Φ.doubledLattice.toAddSubgroup))
      simpa only [QuotientAddGroup.mk_add, add_zero] using he.symm
    have he' := (Φ.doubleCoset_eq_iff (r c.val) 0).mpr hz
    exact c.property ((hr c.val).symm.trans he')
  obtain ⟨u, hup, hu⟩ := F.exists_section_vanish_finite hFi p (fun c : I => p + (r c.val).val) hneq
  obtain ⟨v, hv⟩ := hbg p
  let t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup n := (u.pow 2).mul v
  have htp : t p ≠ 0 := mul_ne_zero (pow_ne_zero 2 hup) hv
  apply Φ.doubleLatticeTheta_trace H J hdouble hJ n t p htp
  intro l hl
  let c : I := ⟨QuotientAddGroup.mk l, hl⟩
  have hcoset : (QuotientAddGroup.mk (r c.val) : C) = QuotientAddGroup.mk l := hr c.val
  have hdiff : (l - r c.val).val ∈ Φ.doubledLattice :=
    (Φ.mem_doubleSubgroup _).mp (QuotientAddGroup.eq_iff_sub_mem.mp hcoset.symm)
  have hzero : t (p + (r c.val).val) = 0 := by
    change u (p + (r c.val).val) ^ 2 * v (p + (r c.val).val) = 0
    rw [hu c, zero_pow (by omega), zero_mul]
  have hh := t.translates ⟨(l - r c.val).val, hdiff⟩ (p + (r c.val).val)
  have harg : p + (r c.val).val + (l - r c.val).val = p + l.val := by
    change p + (r c.val).val + (l.val - (r c.val).val) = p + l.val
    abel
  rw [harg, hzero, mul_zero] at hh
  exact hh

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData.exists_consecutive_generated_powers
    (H : Φ.space →ₗ⋆[ℂ] Φ.space →ₗ[ℂ] ℂ)
    (hsym : ∀ u v, H v u = star (H u v))
    (hpos : ∀ u, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Φ.periodIntegerLattice, ∀ v ∈ Φ.periodIntegerLattice,
      ∃ m : ℤ, (H u v).im = (m : ℝ))
    (J : Φ.AutomorphyFactor) (hJ : ∀ l, ContDiff ℂ ∞ (J.value l))
    (hdouble : ∀ l : Φ.periodIntegerLattice, l ∈ Φ.doubleSubgroup → ∀ z,
      J.value l z = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy (Φ.halfHermitian H) l.val z) :
    ∃ n : ℕ, 0 < n ∧ J.GeneratedPower Φ n ∧ J.GeneratedPower Φ (n + 1) := by
  let : DiscreteTopology Φ.doubledLattice.toAddSubgroup := Φ.doubledLattice_discrete
  have hs := Φ.halfHermitian_symm H hsym
  have hp := Φ.halfHermitian_positive H hpos
  have hi := Φ.halfHermitian_integral H hint
  obtain ⟨F, hFi, _⟩ := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.exists_injective_immersive_family (Φ.halfHermitian H)
    Φ.doubledLattice.toAddSubgroup hs hp hi
  have h2 : ∀ p, ∃ t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup 2, t p ≠ 0 := by
    intro p
    obtain ⟨a, ha⟩ := QuadraticSections.RiemannProjectivityConstruction.exists_thetaPair_ne_zero (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup hs hp p
    exact ⟨QuadraticSections.RiemannProjectivityConstruction.pairSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup hs hp hi a, ha⟩
  have h3 : ∀ p, ∃ t : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup 3, t p ≠ 0 := by
    intro p
    obtain ⟨t, _, ht⟩ := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.cubicBackground (Φ.halfHermitian H) Φ.doubledLattice.toAddSubgroup hs hp hi
      1 (by omega)).nonzero p
    exact ⟨t, ht⟩
  let d := F.degree * Fintype.card {c : Φ.periodIntegerLattice ⧸ Φ.doubleSubgroup // c ≠ 0} * 2
  refine ⟨d + 2, by omega, Φ.interpolation_generated_power H J hJ hdouble F hFi 2 h2, ?_⟩
  change J.GeneratedPower Φ (d + 3)
  exact Φ.interpolation_generated_power H J hJ hdouble F hFi 3 h3

end

end OAI.RepresentationTheory.Theta.Geometric.ConsecutiveSections.CM.Torus.ProjectivePeriodData
