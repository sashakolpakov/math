import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange

/-! # Range Over -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeOver.Constructions

noncomputable section

/-! The actual open-range isomorphism over the complex base preserves
the section vector used in the supported local cycle formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions.Sections OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeSectionPullback.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVectorChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} (j : Y ⟶ N) [IsOpenImmersion j.left]

def rangeOverIso : Y ≅ ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver N j.left.opensRange :=
  Over.isoMk j.left.isoOpensRange (by
    change j.left.isoOpensRange.hom ≫ (j.left.opensRange.ι ≫ N.hom) = Y.hom
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    exact j.w)

theorem rangeOverIso_inclusion :
    (rangeOverIso j).hom ≫ ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion N j.left.opensRange = j := by
  apply Over.OverMorphism.ext
  exact j.left.isoOpensRange_hom_ι

theorem rangeOverIso_section (s : Γ(Y.left, ⊤)) :
    (rangeOverIso j).hom.left.appTop (RangeSectionPullback.Constructions.Sections.rangeSection j.left s) = s := RangeSectionPullback.Constructions.rangeSection_pullback j.left s

variable [IsIntegral Y.left] [Smooth Y.hom] [IsIntegral N.left] [Smooth N.hom]

local instance : Nonempty j.left.opensRange := ⟨⟨j.left (genericPoint Y.left), ⟨_, rfl⟩⟩⟩
local instance : IsIntegral (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver N j.left.opensRange).left :=
  inferInstanceAs (IsIntegral (j.left.opensRange : Scheme))
local instance : Smooth (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeOver N j.left.opensRange).hom :=
  inferInstanceAs (Smooth (j.left.opensRange.ι ≫ N.hom))

theorem rangeBaseSectionVector (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
    (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))
    (hUB : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion N j.left.opensRange)))
    (n : ℕ) (s : Fin n → Γ(Y.left, ⊤)) :
    BaseSectionVector.Constructions.baseSectionVector (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion N j.left.opensRange) U hUB n (fun i => RangeSectionPullback.Constructions.Sections.rangeSection j.left (s i)) =
      BaseSectionVector.Constructions.baseSectionVector j U hU n s := by
  have h := BaseSectionVectorChange.Constructions.baseSectionVector_change (ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion N j.left.opensRange) j (rangeOverIso j).hom
    (rangeOverIso_inclusion j) U hUB hU n (fun i => RangeSectionPullback.Constructions.Sections.rangeSection j.left (s i))
  have hs : (fun i => (rangeOverIso j).hom.left.appTop (RangeSectionPullback.Constructions.Sections.rangeSection j.left (s i))) = s :=
    funext (fun i => rangeOverIso_section j (s i))
  rw [hs] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeOver.Constructions
