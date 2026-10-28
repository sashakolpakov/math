import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportCycles
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ConeResidualStep
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.ChowMoving

/-! # Residual Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ResidualMoving

noncomputable section

/-! The finite residual induction proves the full moving lemma
on an integral smooth projective source, for every positive codimension
and every finite prescribed collection of integral supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap] (hp : 1 ≤ p)
  {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier)

include m hp

theorem bounded (r k : ℕ) (hkr : k + r = p + m) (W : X.DimensionCycleSupport p)
    (hbound : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
        min (p + X.supportCodimension (Z t)) k ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (Finsupp.single W 1) c ∧ c ∈ Proper.SupportCycles.submodule X p Z := by
  induction r generalizing k W with
  | zero =>
    refine ⟨Finsupp.single W 1, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X p _, ?_⟩
    apply Proper.SupportCycles.single_mem
    intro t C hC
    have hZ := Grading.supportDimension_add_codimension X m (Z t)
    have ht : p + X.supportCodimension (Z t) ≤ k := by omega
    simpa only [min_eq_left ht] using hbound t C hC
  | succ r ih =>
    obtain ⟨L, h, hL, _, hdecomp, hres⟩ := ConeResidualStep.exists_coordinates X m p W hp Z
      (fun t => min (p + X.supportCodimension (Z t)) k) hbound
    obtain ⟨c, hc, hcproper⟩ := Cone.ChowMoving.exists_cycle X m L hL h p W Z
    obtain ⟨b, hb, hbproper⟩ := Proper.SupportCycles.lift_cycle X p
      (Proper.SupportCycles.submodule X p Z) (Cone.SupportBound.IntegralCycle.residual X m L hL h p W) (by
        intro D hD
        apply ih (k + 1) (by omega) D
        intro t C hC
        have hr := hres t D hD C hC
        omega)
    refine ⟨c - b, ?_, (Proper.SupportCycles.submodule X p Z).sub_mem hcproper hbproper⟩
    have he : Finsupp.single W (1 : ℚ) - (c - b) =
        (Cone.SupportBound.IntegralCycle.cycle X m L hL h p W - c) -
          (Cone.SupportBound.IntegralCycle.residual X m L hL h p W - b) := by
      rw [hdecomp]
      abel
    change Finsupp.single W (1 : ℚ) - (c - b) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
    rw [he]
    exact (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p).sub_mem hc hb

theorem generator (W : X.DimensionCycleSupport p) :
    ∃ c : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (Finsupp.single W 1) c ∧ c ∈ Proper.SupportCycles.submodule X p Z :=
  bounded X m p hp Z (p + m) 0 (by omega) W (by intro t C _; simp)

theorem cycle (a : X.RationalDimensionCycle p) :
    ∃ c : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a c ∧ c ∈ Proper.SupportCycles.submodule X p Z :=
  Proper.SupportCycles.lift_cycle X p (Proper.SupportCycles.submodule X p Z) a
    (fun W _ => generator X m p hp Z W)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ResidualMoving
