import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology
import OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion

/-! # Generic Fibers -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions

/-! The actual smooth normalization has injective differential and fibers of cardinality one over the constructed generic support open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.Range OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleGraphOpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral D.toOver.left := inferInstanceAs (IsIntegral D.scheme)
local instance : LocallyOfFiniteType D.toOver.hom := inferInstanceAs (LocallyOfFiniteType D.structureMap)
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V D.val).hom := AmbientMap.Constructions.smoothNormalization_smooth V D.val

local notation "ML" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions.sourceOpen D.toOver))) → ℂ
local notation "MS" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val))) → ℂ

theorem sourceToSmooth_analytic_square :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GoodSmoothMap.Constructions.sourceToSmooth D) =
      EtaleGraphOpenImmersion.Constructions.etaleBase (GenericCover.Constructions.coverMap D.toOver) (Open.Constructions.targetToAmbient D) := by
  funext x
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (GoodSmoothMap.Constructions.sourceToSmooth D) (PrincipalBoundary.Constructions.fullAmbientMap V D.val) x).symm.trans
    ((congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (GoodSmoothMap.Constructions.sourceToSmooth_ambient D)).trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (GenericCover.Constructions.coverMap D.toOver) (Open.Constructions.targetToAmbient D) x))

theorem fullAmbientMap_good_differential_injective
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V D.val))
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) x ∈ Open.Constructions.goodAmbient D) :
    Function.Injective (mfderiv 𝓘(ℂ, MS) 𝓘(ℂ, V.analyticModel)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val)) x) := by
  have hr : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GoodSmoothMap.Constructions.sourceToSmooth D)) := by
    rw [GoodSmoothMap.Constructions.Range.sourceToSmooth_analytic_range]
    exact hx
  obtain ⟨y, rfl⟩ := hr
  have ha := ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective (GoodSmoothMap.Constructions.sourceToSmooth D) y
  have hf := EtaleGraphOpenImmersion.Constructions.etaleBase_differential_injective (GenericCover.Constructions.coverMap D.toOver) (Open.Constructions.targetToAmbient D) y
  rw [← sourceToSmooth_analytic_square D] at hf
  rw [mfderiv_comp y
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ω).mdifferentiableAt (by simp))
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (GoodSmoothMap.Constructions.sourceToSmooth D) ω).mdifferentiableAt (by simp))] at hf
  intro v w hvw
  obtain ⟨a, ha'⟩ := ha.surjective v
  obtain ⟨b, hb'⟩ := ha.surjective w
  have hab : a = b := hf
    ((congrArg (mfderiv 𝓘(ℂ, MS) 𝓘(ℂ, V.analyticModel)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GoodSmoothMap.Constructions.sourceToSmooth D) y))
      ha').trans (hvw.trans
        (congrArg (mfderiv 𝓘(ℂ, MS) 𝓘(ℂ, V.analyticModel)
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GoodSmoothMap.Constructions.sourceToSmooth D) y))
          hb').symm))
  exact ha'.symm.trans ((congrArg (mfderiv 𝓘(ℂ, ML) 𝓘(ℂ, MS)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GoodSmoothMap.Constructions.sourceToSmooth D)) y) hab).trans hb')

theorem targetToAmbient_mem_goodAmbient (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (GenericCover.Constructions.targetOpen D.toOver)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D) x ∈ Open.Constructions.goodAmbient D := by
  change ¬ D.inclusion ((GenericCover.Constructions.goodOpen D.toOver).ι (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)) ∈
    ProperImage.Open.Constructions.Construction.supportOpenBoundary D (GenericCover.Constructions.goodOpen D.toOver)
  intro hx
  have he := Set.ext_iff.mp (ProperImage.Open.Constructions.Construction.supportOpenBoundary_preimage D (GenericCover.Constructions.goodOpen D.toOver))
    ((GenericCover.Constructions.goodOpen D.toOver).ι (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x))
  exact (he.mp hx) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x).property

def fullAmbientMap_coverFiberEquiv (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (GenericCover.Constructions.targetOpen D.toOver)) :
    {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (GenericCover.Constructions.sourceOpen D.toOver) | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GenericCover.Constructions.coverMap D.toOver) y = x} ≃
      {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V D.val) |
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D) x} := by
  apply ProperImage.IntrinsicFiberDegree.Constructions.Construction.fiberEquiv_of_commuting_square (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GoodSmoothMap.Constructions.sourceToSmooth D)) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GenericCover.Constructions.coverMap D.toOver))
    (congrFun (sourceToSmooth_analytic_square D))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (GoodSmoothMap.Constructions.sourceToSmooth D)).injective
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (Open.Constructions.targetToAmbient D)).injective x
  intro y hy
  rw [GoodSmoothMap.Constructions.Range.sourceToSmooth_analytic_range]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y ∈ Open.Constructions.goodAmbient D
  rw [show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D) x from hy]
  exact targetToAmbient_mem_goodAmbient D x

theorem fullAmbientMap_genericFiber_card (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (GenericCover.Constructions.targetOpen D.toOver)) :
    Nat.card {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V D.val) |
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D) x} = 1 :=
  (Nat.card_congr (fullAmbientMap_coverFiberEquiv D x).symm).trans (GenericCover.Constructions.coverMap_complexFiber_card D.toOver x)

end AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open

/-! Passing to an actual open subscheme of the smooth normalization preserves the original support, dimension, and all retained fibers that it contains. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericCover.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Open.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.Range
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

local instance : IsIntegral D.toOver.left := inferInstanceAs (IsIntegral D.scheme)
local instance : LocallyOfFiniteType D.toOver.hom := inferInstanceAs (LocallyOfFiniteType D.structureMap)
local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V D.val).hom := AmbientMap.Constructions.smoothNormalization_smooth V D.val

theorem fullAmbientMap_range_subset_support :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val)) ⊆ Set.range D.analyticInclusion := by
  let : IsClosedImmersion D.toAmbient.left := D.inclusion_isClosedImmersion
  rintro _ ⟨y, rfl⟩
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map D.toAmbient)
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  exact ⟨Scheme.Constructions.normalizationMap D.scheme (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y).val,
    (GoodSmoothMap.Constructions.Range.fullAmbientMap_apply D (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying y)).symm⟩

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  (a : X ⟶ AmbientMap.Constructions.smoothNormalizationOver V D.val) [IsOpenImmersion a.left]

local notation "MX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "MS" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val))) → ℂ

def openBase : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → V.analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a

omit [IsOpenImmersion a.left] in
theorem openBase_analytic : ContMDiff 𝓘(ℂ, MX) 𝓘(ℂ, V.analyticModel) ω (openBase D a) :=
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ω).comp (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω)

theorem openBase_good_differential_injective (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hx : openBase D a x ∈ Open.Constructions.goodAmbient D) :
    Function.Injective (mfderiv 𝓘(ℂ, MX) 𝓘(ℂ, V.analyticModel) (openBase D a) x) := by
  have hd := mfderiv_comp x
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ω).mdifferentiableAt (by simp))
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map a ω).mdifferentiableAt (by simp))
  exact (congrArg (fun L : MX →L[ℂ] V.analyticModel => Function.Injective L) hd).mpr
    ((fullAmbientMap_good_differential_injective D (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x) hx).comp
      (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective a x).injective)

omit [IsOpenImmersion a.left] [IsIntegral X.left] [Smooth X.hom] in
theorem openBase_mem_support (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : openBase D a x ∈ Set.range D.analyticInclusion :=
  fullAmbientMap_range_subset_support D ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a x, rfl⟩

include a in
theorem openSource_dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom = D.regularComplexDimension := by
  rw [← Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension, ← a.w]
  exact (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion a.left (AmbientMap.Constructions.smoothNormalizationOver V D.val).hom).trans
    ((AmbientTopology.Constructions.smoothNormalization_dimension V D.val).trans D.regularComplexDimension_eq_supportDimension.symm)

include a in
theorem openGraph_codimension (d : ℕ) :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension MX (V.analyticModel × (Fin d → ℂ)) = p + d := by
  change Module.finrank ℂ (V.analyticModel × (Fin d → ℂ)) - Module.finrank ℂ MX = p + d
  simp only [Module.finrank_prod, Module.finrank_fin_fun, openSource_dimension D a]
  have hd := D.regularComplexDimension_add_codimension
  omega

variable (U : Opens V.analyticSpace)
  (hcover : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (U : Set V.analyticSpace) ⊆
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a))

def openBase_fiberEquiv (u : U) :
    {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | openBase D a y = u.val} ≃
      {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V D.val) |
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y = u.val} := by
  apply ProperImage.IntrinsicFiberDegree.Constructions.Construction.fiberEquiv_of_commuting_square (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map a) id (openBase D a) (fun _ => rfl)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion a).injective Function.injective_id u.val
  intro y hy
  apply hcover
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y ∈ U
  rw [show ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V D.val) y = u.val from hy]
  exact u.property

include hcover in
omit [IsIntegral X.left] [Smooth X.hom] in
theorem openBase_genericFiber_card (u : U) (hu : u.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Open.Constructions.targetToAmbient D))) :
    Nat.card {y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X | openBase D a y = u.val} = 1 := by
  obtain ⟨x, hx⟩ := hu
  have h := fullAmbientMap_genericFiber_card D x
  rw [hx] at h
  exact (Nat.card_congr (openBase_fiberEquiv D a U hcover u)).trans h

end AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open

end

end OAI
