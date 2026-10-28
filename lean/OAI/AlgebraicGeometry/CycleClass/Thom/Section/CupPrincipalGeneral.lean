import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipal
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.SectionRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport

/-! # Cup Principal General -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Detection

/-! At every retained support point, the affine normalization comparison
can be transported back to the original ambient section base. Thus no
affineness or normalization-base restriction is needed for detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseChange.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportDetection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hgood : ∀ x : U, V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D B s →
    x.val ∈ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "I" => Subtype (fun x : U => V.analyticUnderlying (Subtype.val x) ∈ F)

include hgood in
theorem sectionCupClass_eq_principal_on_general_retained_open :
    Cup.Constructions.Class.sectionCupClass D B s U hU = Principal.Constructions.Class.sectionPrincipalClass D B s hs U := by
  classical
  have hlocal : ∀ x : I, ∃ (P : Opens V.analyticSpace) (hPU : P ≤ U),
      x.val.val ∈ P ∧ Cup.Constructions.Class.sectionCupClass D B s P (fun _ hz => hU (hPU hz)) = Principal.Constructions.Class.sectionPrincipalClass D B s hs P := by
    intro x
    have hxB : V.analyticUnderlying x.val.val ∈ B :=
      (Set.ext_iff.mp (NormalizationAffine.OpenRange.Constructions.baseInclusion_analytic_range B) x.val.val).mp (hU x.val.property)
    have hxD : V.analyticUnderlying x.val.val ∈ (D.val : Set V.carrier) := x.property.1
    have hxN : V.analyticUnderlying x.val.val ∈ Normalization.AmbientMap.Constructions.ambientOpen V D.val :=
      Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen_subset_ambient V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs (hgood x.val x.property)
    obtain ⟨C, hC, hxC, hCB, hCN, hNE⟩ := Affine.NormalizationNeighborhood.Constructions.exists_affine_normalization_neighborhood D B _ hxD hxB hxN
    let : Nonempty C := ⟨⟨V.analyticUnderlying x.val.val, hxC⟩⟩
    let : Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C) := hNE
    let : IsAffine (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase C).left := hC
    let P := U ⊓ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver C
    have hPU : P ≤ U := inf_le_left
    have hPC : (P : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C)) := by
      intro y hy
      exact (Set.ext_iff.mp (NormalizationAffine.OpenRange.Constructions.baseInclusion_analytic_range C) y).mpr hy.2
    let sC := (V.carrier.homOfLE hCB).appTop s
    have hsC : Affine.SectionFunction.Constructions.parentSectionFunction D C sC ≠ 0 :=
      fun hz => hs ((BaseRestriction.Constructions.parentSectionFunction_restrict D B C hCB s).symm.trans hz)
    have heC := CupPrincipal.Constructions.sectionCupClass_eq_principal D C hCN sC hsC P hPC
    refine ⟨P, hPU, ⟨x.val.property, hxC⟩, ?_⟩
    apply BaseChange.Constructions.Class.sectionBaseChange_injective D B C hCB s P hPC (2 * q)
    exact (BaseChange.Constructions.Class.sectionCupClass_base_restrict D B C hCB s P (fun _ hz => hU (hPU hz)) hPC).trans
      (heC.trans (BaseChange.Constructions.Class.sectionPrincipalClass_base_restrict D B C hCB s P hPC hs hsC).symm)
  choose P hPU hxP hEq using hlocal
  apply Scheme.OpenSupportDetection.Constructions.relativeClass_eq_of_support_neighborhoods V.toOver F q
    (ClosedSupport.Constructions.sectionClosedSupport_dimension D B s hs) U P hPU hxP
  intro x
  exact (CupRestriction.Constructions.sectionCupClass_restrict D B s U (P x) (hPU x) hU (fun _ hz => hU (hPU x hz))).trans
    ((hEq x).trans (Principal.Constructions.Class.sectionPrincipalClass_restrict D B s hs U (P x) (hPU x)).symm)

end AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Detection

namespace AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions

/-! Supported cycle-section compatibility on an arbitrary actual
ambient open, including all singular parent and normalization boundaries. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Detection OAI.AlgebraicGeometry.CycleClass.Thom.Section.SectionRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens)
  [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

theorem sectionCupClass_eq_principal_general : Cup.Constructions.Class.sectionCupClass D B s U hU = Principal.Constructions.Class.sectionPrincipalClass D B s hs U := by
  apply SectionRestriction.Constructions.retainedRestriction_injective D B s hs U
  let R := SectionRestriction.Constructions.retainedNeighborhood D B s hs U
  have hRU : R ≤ U := inf_le_left
  have hR : (R : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)) :=
    fun _ hx => hU (hRU hx)
  have he : Cup.Constructions.Class.sectionCupClass D B s R hR = Principal.Constructions.Class.sectionPrincipalClass D B s hs R :=
    Detection.sectionCupClass_eq_principal_on_general_retained_open D B s hs R hR
      (fun x hx => BoundaryRemoval.Constructions.retained_supportPoint_good D B s hs x.val hx x.property.2)
  exact (CupRestriction.Constructions.sectionCupClass_restrict D B s U R hRU hU hR).trans
    (he.trans (Principal.Constructions.Class.sectionPrincipalClass_restrict D B s hs U R hRU).symm)

end AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Raw

/-! General singular-parent section compatibility in the original
image-intersection support, ready for enlargement and finite sums. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.Cup.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.Principal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.ParentGraphImage.Constructions.supportCycle V D.val
local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.sectionClosedSupport D B s
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage P U) ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s)
local notation "q" => OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.dimensionCodimension V D.val + 1
local notation "c" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs

theorem principalCycle_supported_intersection (C : Geometric.DimensionCycles.DimensionCycleSupport V q) (hC : c C ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range C.analyticInclusion ⊆ S := by
  intro x hx
  have hxC : V.analyticUnderlying x.val ∈ (C.val : Set V.carrier) := by
    rwa [C.range_analyticInclusion] at hx
  exact (Set.ext_iff.mp (Cup.Constructions.Class.cupSupport_eq_closedSupport D B s U hU) x).mpr
    (Principal.Constructions.Class.principalCycle_supported D B s hs C hC hxC)

theorem cycle_sectionCup_eq_principalClass :
    ImageIntersectionCup.Constructions.imageIntersectionCup (Normalization.BaseImage.Constructions.Class.baseImage P U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement P U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
        (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s))
      (Geometric.DimensionCycles.dimensionCodimension V D.val) 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass P U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S q (Open.SupportedLift.Constructions.restrictCycle V U S q c) := by
  have hi : Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (Cup.Constructions.Class.cupSupport_mapsTo D B s U hU) (2 * q)) := by
    rw [Supported.Transport.Constructions.Class.identityMap_eq_supportCast (TopCat.of U)
      (congrArg Set.compl (Cup.Constructions.Class.cupSupport_eq_closedSupport D B s U hU)) (Cup.Constructions.Class.cupSupport_mapsTo D B s U hU) (2 * q)]
    exact (ConcreteCategory.bijective_of_isIso _).injective
  apply hi
  exact (sectionCupClass_eq_principal_general D B s hs U hU).trans
    ((Principal.Constructions.Class.sectionPrincipalClass_eq_local D B s hs U).trans
      (Open.SupportTransport.Constructions.relativeClassMap_restrict_support_congr V U S {x : U | V.analyticUnderlying x.val ∈ F}
        (Cup.Constructions.Class.cupSupport_eq_closedSupport D B s U hU) q c).symm)

end AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Raw

namespace AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step

/-! One actual principal-divisor step in the original cycle grading,
with its faithful coefficients and supported cup compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Raw OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphSection.Constructions.IntrinsicClass OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GraphSectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.PulledBackSupport OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty B] [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

 def principalStep : Geometric.DimensionCycles.RationalDimensionCycle V (p + 1) :=
  cast (congrArg (Geometric.DimensionCycles.RationalDimensionCycle V) (congrArg (fun n => n + 1) D.property))
    (Normalization.Principal.Constructions.normalizedPrincipalCycle V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs)

omit [Nonempty B] in
theorem principalStep_coefficient (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) :
    principalStep D B s hs C = IntersectionGeometry.principalDivisorCoefficient V.presentation D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) C.val := by
  rcases D with ⟨W, hW⟩
  subst p
  exact Normalization.Principal.Constructions.normalizedPrincipalCycle_coefficient V W _ hs C

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))

local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "S" => Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.BaseImage.Constructions.Class.baseImage D U) ∩ Set.range (OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s)

theorem principalStep_supported (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1)) (hC : principalStep D B s hs C ≠ 0) :
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range C.analyticInclusion ⊆ S := by
  rcases D with ⟨W, hW⟩
  subst p
  exact Raw.principalCycle_supported_intersection ⟨W, rfl⟩ B s hs U hU C hC

theorem cycle_sectionCup_eq_principalStep :
    ImageIntersectionCup.Constructions.imageIntersectionCup (Normalization.BaseImage.Constructions.Class.baseImage D U) (NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU s) (Normalization.GraphSectionCup.Constructions.baseImage_openComplement D U)
      (ImageIntersectionTo.Constructions.PulledBackSupport.pulledBackImage_openComplement (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s)
        (GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B) s))
      p 1 (Normalization.BaseImage.Constructions.Class.baseImageCycleClass D U) (IntrinsicGraphSection.Constructions.IntrinsicClass.baseSectionClass j U hU s) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S (p + 1)
      (Open.SupportedLift.Constructions.restrictCycle V U S (p + 1) (principalStep D B s hs)) := by
  rcases D with ⟨W, hW⟩
  subst p
  exact Raw.cycle_sectionCup_eq_principalClass ⟨W, rfl⟩ B s hs U hU

end AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step

end

end OAI
