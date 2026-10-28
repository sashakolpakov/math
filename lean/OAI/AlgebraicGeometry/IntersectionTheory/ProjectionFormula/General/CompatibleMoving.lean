import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CompatibleSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

/-! # Compatible Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.CompatibleMoving

noncomputable section

/-! The strengthened moving lemma holds in every codimension on every
smooth projective presentation, including disconnected sources. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

local instance component_dimension (K : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety K).presentation.structureMap :=
  Component.Image.component_relativeDimension X m K

theorem positive (p q : ℕ) (hp : 1 ≤ p)
    {τ ι : Type} [Finite τ] [Finite ι] (Z : τ → IrreducibleCloseds X.carrier)
    (B : ι → X.DimensionCycleSupport q) (a : X.RationalDimensionCycle p)
    (hproper : ∀ W ∈ a.support, ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      a - c ∈ CompatibleRelations.submodule X m p q B ∧
      c ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) := by
  let := Fintype.ofFinite (irreducibleComponents X.carrier)
  have hex (K : irreducibleComponents X.carrier) :
      ∃ c : (X.componentVariety K).presentation.RationalDimensionCycle p,
        Component.CycleMaps.restrict X K p a - c ∈ CompatibleRelations.submodule (X.componentVariety K).presentation m p q
          (Component.CompatibleSupports.family X K q B) ∧
        c ∈ Proper.SupportCycles.submodule (X.componentVariety K).presentation p
          (Sum.elim (Component.ProperSupportCycles.family X K Z)
            (fun i => (Component.CompatibleSupports.family X K q B i).val)) :=
    Integral.CompatibleMoving.cycle (X.componentVariety K).presentation m p q hp
      (Component.ProperSupportCycles.family X K Z) (Component.CompatibleSupports.family X K q B)
      (Component.CycleMaps.restrict X K p a) (Component.CompatibleSupports.restrict_proper X K q B p a hproper)
  choose c hc hpos using hex
  let c' := ∑ K, Component.CycleMaps.embed X K p (c K)
  have hrel (K : irreducibleComponents X.carrier) :=
    (CompatibleRelations.mem_iff (X.componentVariety K).presentation m p q
      (Component.CompatibleSupports.family X K q B) (Component.CycleMaps.restrict X K p a) (c K)).mp (hc K)
  refine ⟨c', ?_, ?_⟩
  · apply (CompatibleRelations.mem_iff X m p q B a c').mpr
    constructor
    · apply (Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m p a c').mpr
      intro K
      rw [Component.Principal.Sum.restrict_sum]
      exact (hrel K).1
    · intro i
      apply (Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m (p + q) _ _).mpr
      intro K
      rw [Component.Bilinear.restrict_bilinear, Component.Bilinear.restrict_bilinear,
        Component.Principal.Sum.restrict_sum]
      by_cases hi : ((B i).val : Set X.carrier) ⊆ K.val
      · let j : Component.CompatibleSupports.index X K q B := ⟨i, hi⟩
        have hB : Component.CycleMaps.restrict X K q (Finsupp.single (B i) (1 : ℚ)) =
            Finsupp.single (Component.CompatibleSupports.family X K q B j) 1 := by
          rw [← Component.CompatibleSupports.image X K q B j,
            Component.Bilinear.restrict_single_image]
        rw [hB]
        exact (hrel K).2 j
      · rw [Component.Bilinear.restrict_single_outside X K q (B i) 1 hi, map_zero, map_zero]
        exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl _ (p + q) 0
  · exact Submodule.sum_mem _ fun K _ => Component.CompatibleSupports.embed_position X K q B Z p (c K) (hpos K)

theorem cycle (p q : ℕ)
    {τ ι : Type} [Finite τ] [Finite ι] (Z : τ → IrreducibleCloseds X.carrier)
    (B : ι → X.DimensionCycleSupport q) (a : X.RationalDimensionCycle p)
    (hproper : ∀ W ∈ a.support, ∀ i, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ ((B i).val : Set X.carrier) → p + q ≤ X.supportCodimension C) :
    ∃ c : X.RationalDimensionCycle p,
      a - c ∈ CompatibleRelations.submodule X m p q B ∧
      c ∈ Proper.SupportCycles.submodule X p (Sum.elim Z (fun i => (B i).val)) := by
  by_cases hp : p = 0
  · subst p
    refine ⟨a, ?_, ChowMoving.zero_mem X m (Sum.elim Z (fun i => (B i).val)) a⟩
    rw [sub_self]
    exact (CompatibleRelations.submodule X m 0 q B).zero_mem
  · exact positive X m p q (Nat.pos_of_ne_zero hp) Z B a hproper

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.CompatibleMoving
