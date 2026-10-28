import OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage

/-! # Section Zero Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionZeroSupport.Constructions

noncomputable section

/-! On the actual affine base, the global algebraic support is exactly
the cycle-section image support used by the relative cup product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (U : Opens V.analyticSpace)
  (hUJ : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

omit D in
theorem baseOpenLift_unit_iff (x : U) :
    V.analyticUnderlying x.val ∈ V.carrier.basicOpen (B.topIso.hom s) ↔
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ x) s ≠ 0 := by
  let y := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ x)
  have he : B.ι y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying_map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ x)).symm.trans
      (congrArg ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ x))
  have hm : B.ι y ∈ V.carrier.basicOpen (B.topIso.hom s) ↔ y ∈ B.toScheme.basicOpen s := by
    rw [← Open.SectionBasic.Constructions.openSection_basicOpen_image B s]
    constructor
    · rintro ⟨z, hz, hzy⟩
      exact B.ι.isOpenEmbedding.injective hzy ▸ hz
    · exact fun hy => ⟨y, hy, rfl⟩
  exact ((congrArg (fun z : V.carrier => z ∈ V.carrier.basicOpen (B.topIso.hom s)) he).to_iff.symm.trans hm).trans
    (GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ x))

omit D in
theorem baseSectionImage_range : Set.range (NormalizationAffine.SectionSupport.Constructions.baseSectionImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ s) =
    {x : U | V.analyticUnderlying x.val ∉ V.carrier.basicOpen (B.topIso.hom s)} := by
  ext x
  rw [ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_range, GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  change DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ x) s = 0 ↔
    V.analyticUnderlying x.val ∉ V.carrier.basicOpen (B.topIso.hom s)
  simpa only [not_ne_iff] using (not_congr (baseOpenLift_unit_iff B s U hUJ x)).symm

 theorem sectionClosedSupport_analytic_range :
    {x : U | V.analyticUnderlying x.val ∈ Section.ClosedSupport.Constructions.sectionClosedSupport D B s} =
      Set.range (Normalization.BaseImage.Constructions.Class.baseImage D U) ∩ Set.range (NormalizationAffine.SectionSupport.Constructions.baseSectionImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUJ s) := by
  rw [Normalization.BaseImage.Constructions.Class.baseImage_range, baseSectionImage_range]
  ext x
  change (V.analyticUnderlying x.val ∈ (D.val : Set V.carrier) ∧
      V.analyticUnderlying x.val ∉ V.carrier.basicOpen (B.topIso.hom s)) ↔
    (x.val ∈ Set.range D.analyticInclusion ∧ V.analyticUnderlying x.val ∉ V.carrier.basicOpen (B.topIso.hom s))
  rw [D.range_analyticInclusion]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionZeroSupport.Constructions
