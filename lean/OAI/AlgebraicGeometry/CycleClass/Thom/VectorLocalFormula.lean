import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFormulaTransport
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFilter
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap

/-! # Vector Local Formula -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions

noncomputable section

/-! Uniform local formulas for section-vector classes and their exact
geometric induction step, including the removal of components away
from the chosen scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFormulaTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorRecursion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFilter.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkMap.Constructions.VectorGerms OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.CycleSectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def HasLocalVectorFormula (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (B : V.carrier.Opens) [Nonempty B]
    (p n d : ℕ) (hd : p + n = d) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (c : Geometric.DimensionCycles.RationalDimensionCycle V p) (z : Geometric.DimensionCycles.RationalDimensionCycle V d) (C : V.carrier.Opens) : Prop :=
  ∀ (U : Opens V.analyticSpace) (_hUC : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver C)
    (hUB : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
    {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ),
    (∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u) →
    Cycle.Vector.Constructions.Class.cycleVectorClassAt V B U hUB u p n d hd s hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Cycle.Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Cycle.Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s) d z)

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (p n d : ℕ) (hd : p + (n + 1) = d)
  (B C : V.carrier.Opens) (hCB : C ≤ B) [Nonempty B] [Nonempty C]
  (x : V.carrier) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left, ⊤))
  (ha : a - Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r ∈ Ideal.span (Set.range (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))))
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hne : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C))
  (hs : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D C a ≠ 0)
  (z : Geometric.DimensionCycles.RationalDimensionCycle V d) (D : V.carrier.Opens) (hDC : D ≤ C)

local notation "sC" => (fun i => OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))
local notation "rC" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB r
local notation "c₁" => OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions.originalPrincipalStepSum V p C a c hne hs
local notation "c₂" => OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions.cycleAtPoint V (p + 1) x c₁
local notation "N" => OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions.pointNeighborhood V (p + 1) x c₁ C

include ha hDC in
theorem localFormula_of_filtered_step
    (h : HasLocalVectorFormula V C (p + 1) n d (by omega) sC c₂ z D) :
    HasLocalVectorFormula V B p (n + 1) d hd (Fin.cons r s) c z (D ⊓ N) := by
  intro U hUN hUB L u hu hcu
  have hUD : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver D := fun _ hy => (hUN hy).1
  have hUP : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver N := fun _ hy => (hUN hy).2
  have hUC : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C)) :=
    fun _ hy => Section.StalkMap.Constructions.VectorGerms.analyticOpen_le_baseRange V C (Section.StalkMap.Constructions.VectorGerms.analyticOpen_mono V hDC (hUD hy))
  let u₁ := (Subtype.val : {y : U // y ∈ Set.range u ∩ Set.range (NormalizationAffine.SectionSupport.Constructions.baseSectionImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC a)} → U)
  have hu₁ : IsOpen (Set.range u₁)ᶜ := Cycle.VectorRecursion.Constructions.cutImage_openComplement V C a U hUC u hu
  have hc₁ : ∀ E : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1), c₁ E ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range E.analyticInclusion ⊆ Set.range u₁ := by
    intro E hE
    rw [Subtype.range_coe]
    apply Finite.CycleSectionClass.Constructions.cycleSectionStep_supported V p C a U hUC u c hcu hne hs E
    rwa [Finite.SectionEuler.Constructions.cycleSectionStep_eq_sum]
  have hc₂ : ∀ E : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1), c₂ E ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range E.analyticInclusion ⊆ Set.range u₁ :=
    fun E hE => hc₁ E (Cycle.AtPoint.Constructions.cycleAtPoint_ne_zero V (p + 1) x c₁ E hE).1
  have htail := (Cycle.VectorFilter.Constructions.cycleVectorClassAt_cycleAtPoint V C U hUC u₁ (p + 1) n d (by omega)
    sC hu₁ c₁ x C hUP hc₁).trans (h U hUD hUC u₁ hu₁ hc₂)
  have hfull := Cycle.VectorFormulaTransport.Constructions.formula_of_step V C U hUC u p n d sC hu c z a hd hcu hne hs htail
  apply Cycle.VectorFormulaTransport.Constructions.formula_of_base_change V B C hCB U hUB hUC u p (n + 1) d (Fin.cons r s) hu c z hd
  have hv : (fun i : Fin (n + 1) => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB
      ((Fin.cons r s : Fin (n + 1) → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) i)) = Fin.cons rC sC := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hv]
  apply Cycle.VectorFormulaTransport.Constructions.formula_of_head_change V C U hUC u p n d sC hu c z rC (a - rC) ha hd
  have he : rC + (a - rC) = a := by ring
  rw [he]
  exact hfull

end

end OAI.AlgebraicGeometry.CycleClass.Thom.VectorLocalFormula.Constructions
