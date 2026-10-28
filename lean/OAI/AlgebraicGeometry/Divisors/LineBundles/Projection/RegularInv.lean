import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportProjections
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.StratumIso

/-! # Regular Inv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv.BundleCycles

noncomputable section

section

/-! The regular complex points of the actual projection inverse-image
support form the product of the smooth factor with the regular support.
The identification respects both literal ambient projections. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductProjections.Constructions
open scoped _root_.Manifold ContDiff

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType Z.hom]

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod

local instance : LocallyOfFiniteType (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B).hom :=
  CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType B Y.hom
local instance : LocallyOfFinitePresentation (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom))
local instance : LocallyOfFiniteType (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C).hom :=
  CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType C Z.hom
local instance : LocallyOfFinitePresentation (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CycleClass.Geometric.SupportFiniteType.supportStructureMap C Z.hom))

def projectionRegularPointsHomeomorph : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Z C) ≃ₜ
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y B)) :=
  (CycleClass.Thom.Regular.ProductProjections.Constructions.regularProductPointsHomeomorph X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
    (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
    (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod)).trans
    ((LineBundles.Smooth.StratumIso.BundleCycles.smoothStratumPointsHomeomorph X).prodCongr (Homeomorph.refl _))

theorem projectionRegularPointsHomeomorph_fst (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Z C)) :
    (projectionRegularPointsHomeomorph X Y B Z πX πY hprod z).1 =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Z C z) := by
  have h := CycleClass.Thom.Regular.ProductProjections.Constructions.regularFst_inclusion X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
    (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
    (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod)
  change (z ≫ CycleClass.Thom.Regular.ProductProjections.Constructions.regularFst X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
      (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
      (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod)) ≫
    CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion X =
      (z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Z C) ≫ πX
  have h' : CycleClass.Thom.Regular.ProductProjections.Constructions.regularFst X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
      (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
      (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod) ≫
      CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion X = CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Z C ≫ πX := by
    have h₁ := congrArg
      (fun k => CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C) ≫ k)
      (SupportProjections.BundleCycles.projectionReducedFst_inclusion X Y B Z πX πY hprod)
    exact h.trans (h₁.trans (Category.assoc _ _ _).symm)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => z ≫ k) h').trans (Category.assoc _ _ _).symm)

theorem projectionRegularPointsHomeomorph_snd (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Z C)) :
    CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y B (projectionRegularPointsHomeomorph X Y B Z πX πY hprod z).2 =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Z C z) := by
  have h := CycleClass.Thom.Regular.ProductProjections.Constructions.regularSnd_inclusion X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
    (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
    (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod)
  change (z ≫ CycleClass.Thom.Regular.ProductProjections.Constructions.regularSnd X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
      (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
      (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod)) ≫
    (CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B) =
      (z ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Z C) ≫ πY
  have h' : CycleClass.Thom.Regular.ProductProjections.Constructions.regularSnd X (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C)
      (SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod) (SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod)
      (SupportDimension.BundleCycles.projectionReducedIsLimit X Y B Z πX πY hprod) ≫
      (CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B) ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B) =
        CycleClass.Thom.Scheme.RegularSupport.Constructions.regularToAmbient Z C ≫ πY := by
    have h₁ := congrArg (fun k => k ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B) h
    have h₂ := congrArg
      (fun k => CycleClass.Thom.Regular.ProductOver.Constructions.regularOverInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z C) ≫ k)
      (SupportProjections.BundleCycles.projectionReducedSnd_inclusion X Y B Z πX πY hprod)
    exact (Category.assoc _ _ _).symm.trans
      (h₁.trans ((Category.assoc _ _ _).trans (h₂.trans (Category.assoc _ _ _).symm)))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => z ≫ k) h').trans (Category.assoc _ _ _).symm)

end

section

/-! Under a genuine product projection, the full support, regular locus,
and singular boundary have their exact inverse-image descriptions on
complex points. Hence the regular ambient open is the full inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType Z.hom]

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph X Y Z πX πY hprod

omit [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] in
theorem projectionSupportInclusion_range :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Z C) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B) := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
  ext z
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ (C : Set Z.left) ↔ _
  rw [ReducedSupport.BundleCycles.projectionIrreducibleSupport_coe]
  rfl

theorem projectionRegularInclusion_range :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Z C) = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y B) := by
  let r := projectionRegularPointsHomeomorph X Y B Z πX πY hprod
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨(r c).2, projectionRegularPointsHomeomorph_snd X Y B Z πX πY hprod c⟩
  · rintro ⟨b, hb⟩
    let c := r.symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX z, b)
    refine ⟨c, (e).injective ?_⟩
    apply Prod.ext
    · have h := projectionRegularPointsHomeomorph_fst X Y B Z πX πY hprod c
      change (r (r.symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX z, b))).1 = _ at h
      rw [Homeomorph.apply_symm_apply] at h
      exact h.symm
    · have h := projectionRegularPointsHomeomorph_snd X Y B Z πX πY hprod c
      change CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y B (r (r.symm (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX z, b))).2 = _ at h
      rw [Homeomorph.apply_symm_apply] at h
      exact h.symm.trans hb

theorem projectionAnalyticBoundary :
    CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary Z C = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ⁻¹' CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary Y B := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq, CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary_eq, projectionSupportInclusion_range,
    projectionRegularInclusion_range, Set.preimage_sdiff]

theorem projectionRegularAmbientOpen :
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Z C : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ⁻¹' (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  change (CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary Z C)ᶜ = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ⁻¹' (CycleClass.Thom.Scheme.RegularSupport.Constructions.analyticBoundary Y B)ᶜ
  rw [projectionAnalyticBoundary, Set.preimage_compl]

end

/-! The entire regular ambient neighborhood of a projection support is
the genuine product of the smooth factor and the base regular neighborhood. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType Z.hom]

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph X Y Z πX πY hprod
local notation "G" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Z C
local notation "H" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions.regularAmbientOpen Y B

theorem projectionRegularAmbient_mem (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) :
    z ∈ G ↔ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY z ∈ H :=
  Set.ext_iff.mp (projectionRegularAmbientOpen X Y B Z πX πY hprod) z

def projectionRegularAmbientMap (z : G) : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX z.val,
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY z.val, (projectionRegularAmbient_mem X Y B Z πX πY hprod z.val).mp z.property⟩)

def projectionRegularAmbientInv (xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H) : G :=
  ⟨(e).symm (xy.1, xy.2.val), by
    apply (projectionRegularAmbient_mem X Y B Z πX πY hprod _).mpr
    have h := congrArg Prod.snd ((e).apply_symm_apply (xy.1, xy.2.val))
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ((e).symm (xy.1, xy.2.val)) = xy.2.val at h
    rw [h]
    exact xy.2.property⟩

theorem projectionRegularAmbient_left_inv (z : G) :
    projectionRegularAmbientInv X Y B Z πX πY hprod (projectionRegularAmbientMap X Y B Z πX πY hprod z) = z :=
  Subtype.ext ((e).symm_apply_apply z.val)

theorem projectionRegularAmbient_right_inv (xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H) :
    projectionRegularAmbientMap X Y B Z πX πY hprod (projectionRegularAmbientInv X Y B Z πX πY hprod xy) = xy := by
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πX ((e).symm (xy.1, xy.2.val)) = xy.1 :=
    congrArg Prod.fst ((e).apply_symm_apply (xy.1, xy.2.val))
  have hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πY ((e).symm (xy.1, xy.2.val)) = xy.2.val :=
    congrArg Prod.snd ((e).apply_symm_apply (xy.1, xy.2.val))
  exact Prod.ext hx (Subtype.ext hy)

theorem projectionRegularAmbientMap_continuous : Continuous (projectionRegularAmbientMap X Y B Z πX πY hprod) :=
  ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πX).comp continuous_subtype_val).prodMk
    (((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πY).comp continuous_subtype_val).subtype_mk _)

theorem projectionRegularAmbientInv_continuous : Continuous (projectionRegularAmbientInv X Y B Z πX πY hprod) :=
  ((e).symm.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

def projectionRegularAmbientHomeomorph : G ≃ₜ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × H) where
  toFun := projectionRegularAmbientMap X Y B Z πX πY hprod
  invFun := projectionRegularAmbientInv X Y B Z πX πY hprod
  left_inv := projectionRegularAmbient_left_inv X Y B Z πX πY hprod
  right_inv := projectionRegularAmbient_right_inv X Y B Z πX πY hprod
  continuous_toFun := projectionRegularAmbientMap_continuous X Y B Z πX πY hprod
  continuous_invFun := projectionRegularAmbientInv_continuous X Y B Z πX πY hprod

theorem projectionRegularAmbientHomeomorph_inclusion (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Z C)) :
    projectionRegularAmbientHomeomorph X Y B Z πX πY hprod (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Z C z) =
      Prod.map (id : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularComplementInclusion Y B)
        (projectionRegularPointsHomeomorph X Y B Z πX πY hprod z) := by
  apply Prod.ext
  · exact (projectionRegularPointsHomeomorph_fst X Y B Z πX πY hprod z).symm
  · exact Subtype.ext (projectionRegularPointsHomeomorph_snd X Y B Z πX πY hprod z).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularInv.BundleCycles
