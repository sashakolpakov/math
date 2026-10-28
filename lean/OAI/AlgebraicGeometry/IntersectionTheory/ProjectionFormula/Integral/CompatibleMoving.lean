import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleResidualCoordinates
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.CompatibleMoving

/-! # Compatible Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.CompatibleMoving

noncomputable section

/-! The residual moving induction preserves the native intersection
class with every fixed support already met properly by the original
cycle, while imposing any additional finite proper-position constraints. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
  (m p q : ℕ) [SmoothOfRelativeDimension m X.structureMap] (hp : 1 ≤ p)
  {τ ι : Type} [Finite τ] [Finite ι] (Z : τ → IrreducibleCloseds X.carrier)
  (B : ι → X.DimensionCycleSupport q)

include hp in
theorem bounded (r k : ℕ) (hkr : k + r = p + m) (W : X.DimensionCycleSupport p)
    (hbound : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
        min (p + X.supportCodimension (Z t)) k ≤ X.supportCodimension C)
    (hproper : ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      Finsupp.single W 1 - c ∈ CompatibleRelations.submodule X m p q B ∧
      c ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) := by
  induction r generalizing k W with
  | zero =>
    refine ⟨Finsupp.single W 1, ?_, ?_⟩
    · rw [sub_self]
      exact (CompatibleRelations.submodule X m p q B).zero_mem
    · apply Proper.SupportCycles.single_mem
      intro t C hC
      cases t with
      | inl t =>
        change p + X.supportCodimension (Z t) ≤ X.supportCodimension C
        have hZ := Grading.supportDimension_add_codimension X m (Z t)
        have ht : p + X.supportCodimension (Z t) ≤ k := by omega
        simpa only [min_eq_left ht] using hbound t C hC
      | inr i =>
        change p + X.supportCodimension (B i).val ≤ X.supportCodimension C
        rw [(B i).property]
        exact hproper i C hC
  | succ r ih =>
    obtain ⟨L, h, hL, hdecomp, hcone, hres, hresproper⟩ :=
      CompatibleResidualCoordinates.exists_coordinates X m p q hp W Z B
        (fun t => min (p + X.supportCodimension (Z t)) k) hbound hproper
    obtain ⟨c, hc, hcproper⟩ := Cone.CompatibleMoving.exists_cycle X m L hL h p q W Z B hcone
    let R := CompatibleRelations.submodule X m p q B
    let G := Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val))
    obtain ⟨b, hb, hbproper⟩ := CompatibleRelations.lift_cycle X p R G
      (Cone.SupportBound.IntegralCycle.residual X m L hL h p W) (by
        intro D hD
        apply ih (k + 1) (by omega) D
        · intro t C hC
          have hr := hres t D hD C hC
          omega
        · exact fun i C hC => hresproper i D hD C hC)
    refine ⟨c - b, ?_, G.sub_mem hcproper hbproper⟩
    have he : Finsupp.single W (1 : ℚ) - (c - b) =
        (Cone.SupportBound.IntegralCycle.cycle X m L hL h p W - c) -
          (Cone.SupportBound.IntegralCycle.residual X m L hL h p W - b) := by
      rw [hdecomp]
      abel
    rw [he]
    exact R.sub_mem hc hb

include hp in
theorem generator (W : X.DimensionCycleSupport p)
    (hproper : ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      Finsupp.single W 1 - c ∈ CompatibleRelations.submodule X m p q B ∧
      c ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) :=
  bounded X m p q hp Z B (p + m) 0 (by omega) W (by intro t C _; simp) hproper

include hp in
theorem cycle (a : X.RationalDimensionCycle p)
    (hproper : ∀ W ∈ a.support, ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      a - c ∈ CompatibleRelations.submodule X m p q B ∧
      c ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) :=
  CompatibleRelations.lift_cycle X p
    (CompatibleRelations.submodule X m p q B)
    (Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val))) a
    (fun W hW => generator X m p q hp Z B W (hproper W hW))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.CompatibleMoving
