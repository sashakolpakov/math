import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductProjections
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement

/-! # Product Point Ranges -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints

/-! The native regular analytic locus of the genuine product cycle support
is the holomorphic product of the native regular loci of its factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularLocusComplement
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOverIso.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportPoints.Constructions
  Regular.ProductProjections.Constructions Product.PresentationPoints.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : LocallyOfFiniteType V.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType V.structureMap)
local instance {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (A : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    LocallyOfFinitePresentation A.toOver.hom := inferInstanceAs (LocallyOfFinitePresentation A.structureMap)
local instance {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (A : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsIntegral A.toOver.left := inferInstanceAs (IsIntegral A.scheme)

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B

def integralProductSupportFst : (C).toOver ⟶ A.toOver :=
  Product.SupportOverIso.Constructions.reducedProductFst V.toOver W.toOver A.val B.val T.toOver πV πW hprod

def integralProductSupportSnd : (C).toOver ⟶ B.toOver :=
  Product.SupportOverIso.Constructions.reducedProductSnd V.toOver W.toOver A.val B.val T.toOver πV πW hprod

def integralProductSupportIsLimit : IsLimit (BinaryFan.mk
    (integralProductSupportFst V W T πV πW hprod p q A B)
    (integralProductSupportSnd V W T πV πW hprod p q A B)) :=
  Product.SupportOverIso.Constructions.reducedProductIsLimit V.toOver W.toOver A.val B.val T.toOver πV πW hprod

def integralProductRegularHomeomorph : (C).regularAnalyticSpace ≃ₜ
    (A.regularAnalyticSpace × B.regularAnalyticSpace) :=
  Regular.ProductProjections.Constructions.regularProductPointsHomeomorph A.toOver B.toOver (C).toOver
    (integralProductSupportFst V W T πV πW hprod p q A B)
    (integralProductSupportSnd V W T πV πW hprod p q A B)
    (integralProductSupportIsLimit V W T πV πW hprod p q A B)

theorem integralProductRegularHomeomorph_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, (C).regularAnalyticModel)
      (𝓘(ℂ, A.regularAnalyticModel).prod 𝓘(ℂ, B.regularAnalyticModel)) r
      (integralProductRegularHomeomorph V W T πV πW hprod p q A B) :=
  Regular.ProductProjections.Constructions.regularProductPointsHomeomorph_contMDiff A.toOver B.toOver (C).toOver
    (integralProductSupportFst V W T πV πW hprod p q A B)
    (integralProductSupportSnd V W T πV πW hprod p q A B)
    (integralProductSupportIsLimit V W T πV πW hprod p q A B) r

theorem integralProductRegularHomeomorph_symm_contMDiff (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, A.regularAnalyticModel).prod 𝓘(ℂ, B.regularAnalyticModel))
      𝓘(ℂ, (C).regularAnalyticModel) r
      (integralProductRegularHomeomorph V W T πV πW hprod p q A B).symm :=
  Regular.ProductProjections.Constructions.regularProductPointsHomeomorph_symm_contMDiff A.toOver B.toOver (C).toOver
    (integralProductSupportFst V W T πV πW hprod p q A B)
    (integralProductSupportSnd V W T πV πW hprod p q A B)
    (integralProductSupportIsLimit V W T πV πW hprod p q A B) r

theorem integralProductRegularHomeomorph_fst (z : (C).regularAnalyticSpace) :
    A.regularAnalyticToAmbient (integralProductRegularHomeomorph V W T πV πW hprod p q A B z).1 =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV ((C).regularAnalyticToAmbient z) := by
  have h := Regular.ProductProjections.Constructions.regularFst_inclusion A.toOver B.toOver (C).toOver
    (integralProductSupportFst V W T πV πW hprod p q A B)
    (integralProductSupportSnd V W T πV πW hprod p q A B)
    (integralProductSupportIsLimit V W T πV πW hprod p q A B)
  have hi := Product.SupportOverIso.Constructions.reducedProductFst_inclusion V.toOver W.toOver A.val B.val T.toOver πV πW hprod
  change (z ≫ Regular.ProductProjections.Constructions.regularFst A.toOver B.toOver (C).toOver _ _ _) ≫
    (A.regularToSupport ≫ A.toAmbient) = (z ≫ ((C).regularToSupport ≫ (C).toAmbient)) ≫ πV
  simp only [Category.assoc]
  have h' : Regular.ProductProjections.Constructions.regularFst A.toOver B.toOver (C).toOver _ _ _ ≫ A.regularToSupport =
      (C).regularToSupport ≫ integralProductSupportFst V W T πV πW hprod p q A B := h
  rw [← Category.assoc (Regular.ProductProjections.Constructions.regularFst A.toOver B.toOver (C).toOver _ _ _) A.regularToSupport, h']
  change z ≫ ((C).regularToSupport ≫ (Product.SupportOverIso.Constructions.reducedProductFst V.toOver W.toOver A.val B.val T.toOver πV πW hprod ≫
    Product.SupportPoints.Constructions.supportOverInclusion V.toOver A.val)) = _
  rw [hi]
  rfl

theorem integralProductRegularHomeomorph_snd (z : (C).regularAnalyticSpace) :
    B.regularAnalyticToAmbient (integralProductRegularHomeomorph V W T πV πW hprod p q A B z).2 =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW ((C).regularAnalyticToAmbient z) := by
  have h := Regular.ProductProjections.Constructions.regularSnd_inclusion A.toOver B.toOver (C).toOver
    (integralProductSupportFst V W T πV πW hprod p q A B)
    (integralProductSupportSnd V W T πV πW hprod p q A B)
    (integralProductSupportIsLimit V W T πV πW hprod p q A B)
  have hi := Product.SupportOverIso.Constructions.reducedProductSnd_inclusion V.toOver W.toOver A.val B.val T.toOver πV πW hprod
  change (z ≫ Regular.ProductProjections.Constructions.regularSnd A.toOver B.toOver (C).toOver _ _ _) ≫
    (B.regularToSupport ≫ B.toAmbient) = (z ≫ ((C).regularToSupport ≫ (C).toAmbient)) ≫ πW
  simp only [Category.assoc]
  have h' : Regular.ProductProjections.Constructions.regularSnd A.toOver B.toOver (C).toOver _ _ _ ≫ B.regularToSupport =
      (C).regularToSupport ≫ integralProductSupportSnd V W T πV πW hprod p q A B := h
  rw [← Category.assoc (Regular.ProductProjections.Constructions.regularSnd A.toOver B.toOver (C).toOver _ _ _) B.regularToSupport, h']
  change z ≫ ((C).regularToSupport ≫ (Product.SupportOverIso.Constructions.reducedProductSnd V.toOver W.toOver A.val B.val T.toOver πV πW hprod ≫
    Product.SupportPoints.Constructions.supportOverInclusion W.toOver B.val)) = _
  rw [hi]
  rfl

end AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints

namespace AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions

/-! Exact analytic images of the actual product support and its regular
locus, and the resulting containment of product regular neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions
  Product.PresentationPoints.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : LocallyOfFiniteType V.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType V.structureMap)

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph V.toOver W.toOver T.toOver πV πW hprod

theorem integralProductSupport_range : Set.range (C).analyticInclusion =
    e ⁻¹' (Set.range A.analyticInclusion ×ˢ Set.range B.analyticInclusion) := by
  rw [Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion, Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion,
    Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion]
  ext z
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈
    (Product.SupportScheme.Constructions.productIrreducibleSupport V.toOver W.toOver A.val B.val T.toOver πV πW hprod : Set T.toOver.left) ↔ _
  rw [Product.SupportScheme.Constructions.productIrreducibleSupport_coe]
  rfl

theorem integralProductRegular_range : Set.range (C).regularAnalyticToAmbient =
    e ⁻¹' (Set.range A.regularAnalyticToAmbient ×ˢ Set.range B.regularAnalyticToAmbient) := by
  let r := RegularPoints.integralProductRegularHomeomorph V W T πV πW hprod p q A B
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨(r c).1, RegularPoints.integralProductRegularHomeomorph_fst V W T πV πW hprod p q A B c⟩,
      ⟨(r c).2, RegularPoints.integralProductRegularHomeomorph_snd V W T πV πW hprod p q A B c⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨r.symm (a, b), (e).injective ?_⟩
    apply Prod.ext
    · have h := RegularPoints.integralProductRegularHomeomorph_fst V W T πV πW hprod p q A B (r.symm (a, b))
      change A.regularAnalyticToAmbient (r (r.symm (a, b))).1 = _ at h
      rw [Homeomorph.apply_symm_apply] at h
      exact h.symm.trans ha
    · have h := RegularPoints.integralProductRegularHomeomorph_snd V W T πV πW hprod p q A B (r.symm (a, b))
      change B.regularAnalyticToAmbient (r (r.symm (a, b))).2 = _ at h
      rw [Homeomorph.apply_symm_apply] at h
      exact h.symm.trans hb

theorem integralProduct_regularAmbient_contains (z : T.analyticSpace)
    (ha : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV z ∈ A.regularAmbientOpen)
    (hb : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW z ∈ B.regularAmbientOpen) : z ∈ (C).regularAmbientOpen := by
  change z ∉ (C).analyticSingularBoundary
  rw [Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary_eq_sdiff,
    integralProductSupport_range, integralProductRegular_range]
  rintro ⟨⟨hza, hzb⟩, hn⟩
  apply hn
  constructor
  · by_contra h
    exact ha ((A.analyticSingularBoundary_eq_sdiff).symm ▸ ⟨hza, h⟩)
  · by_contra h
    exact hb ((B.analyticSingularBoundary_eq_sdiff).symm ▸ ⟨hzb, h⟩)

end AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions

end

end OAI
