import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Support Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportCycles

noncomputable section

/-! Cycles meeting a prescribed collection of supports properly form
a submodule. Moving the finitely many supported generators moves a cycle. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) {τ : Type}
  (Z : τ → IrreducibleCloseds X.carrier)

def submodule : Submodule ℚ (X.RationalDimensionCycle p) where
  carrier := {c | ∀ t, ∀ D ∈ c.support, ∀ C : IrreducibleCloseds X.carrier,
    (C : Set X.carrier) ⊆ (D.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
      p + X.supportCodimension (Z t) ≤ X.supportCodimension C}
  zero_mem' := by
    intro t D hD
    simp at hD
  add_mem' := by
    intro a b ha hb t D hD
    rcases Finset.mem_union.mp (Finsupp.support_add hD) with hD | hD
    · exact ha t D hD
    · exact hb t D hD
  smul_mem' := by
    intro r a ha t D hD
    exact ha t D (Finsupp.support_smul hD)

theorem single_mem (W : X.DimensionCycleSupport p)
    (hW : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ (Z t : Set X.carrier) →
        p + X.supportCodimension (Z t) ≤ X.supportCodimension C) :
    Finsupp.single W (1 : ℚ) ∈ submodule X p Z := by
  intro t D hD
  have he : D = W := by
    simpa only [Finsupp.support_single W one_ne_zero, Finset.mem_singleton] using hD
  subst D
  exact hW t

omit Z in
theorem lift_cycle (G : Submodule ℚ (X.RationalDimensionCycle p)) (a : X.RationalDimensionCycle p)
    (h : ∀ D ∈ a.support, ∃ b : X.RationalDimensionCycle p,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (Finsupp.single D 1) b ∧ b ∈ G) :
    ∃ b : X.RationalDimensionCycle p, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a b ∧ b ∈ G := by
  choose b hb hg using fun D : a.support => h D.val D.property
  let c := ∑ D : a.support, a D.val • b D
  refine ⟨c, ?_, ?_⟩
  · have hs : (∑ D : a.support, a D.val • Finsupp.single D.val (1 : ℚ)) = a := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Finset.sum_coe_sort a.support (fun D => Finsupp.single D (a D))).trans a.sum_single
    have hr : (∑ D : a.support, a D.val • (Finsupp.single D.val (1 : ℚ) - b D)) ∈
        CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p :=
      Submodule.sum_mem _ (fun D _ => Submodule.smul_mem _ _ (hb D))
    change a - (∑ D : a.support, a D.val • b D) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p
    simpa only [smul_sub, Finset.sum_sub_distrib, hs] using hr
  · exact Submodule.sum_mem G (fun D _ => Submodule.smul_mem G _ (hg D))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.SupportCycles
