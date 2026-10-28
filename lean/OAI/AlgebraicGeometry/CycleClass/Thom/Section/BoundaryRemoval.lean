import OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval

/-! # Boundary Removal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval.Constructions

noncomputable section

/-! The part of the normalization boundary inside the section support
has strictly larger codimension. Removing it preserves the actual
relative cohomology in the cycle-section degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportRemoval.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)
local instance : AlgebraicGeometry.IsNoetherian V.toOver.left := inferInstanceAs (AlgebraicGeometry.IsNoetherian V.carrier)

def sectionExceptional : Closeds V.carrier :=
  Normalization.PrincipalZero.Constructions.BoundaryUnion.commonBoundary V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs ⊓ ClosedSupport.Constructions.sectionClosedSupport D B s

 theorem sectionExceptional_dimension (Z : IrreducibleCloseds V.carrier)
    (hZ : (Z : Set V.carrier) ⊆ sectionExceptional D B s hs) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + (Geometric.DimensionCycles.dimensionCodimension V D.val + 2) ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  have hc := Normalization.PrincipalZero.Constructions.BoundaryUnion.commonBoundary_codimension V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs Z (fun _ hz => (hZ hz).1)
  have hd := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V Z
  omega

 theorem sectionExceptional_complement_mapsTo (U : Opens V.analyticSpace) :
    {x : U | V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D B s}ᶜ ⊆
      {x : U | V.analyticUnderlying x.val ∈ sectionExceptional D B s hs}ᶜ :=
  fun _ hx he => hx he.2

 theorem section_relativeRestriction_isIso (U : Opens V.analyticSpace) :
    IsIso (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | V.analyticUnderlying x.val ∈ sectionExceptional D B s hs}ᶜ
      {x : U | V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D B s}ᶜ
      (2 * (Geometric.DimensionCycles.dimensionCodimension V D.val + 1))) :=
  Scheme.OpenSupportRemoval.Constructions.open_relativeRestriction_isIso V.toOver (sectionExceptional D B s hs) (Geometric.DimensionCycles.dimensionCodimension V D.val + 2)
    (sectionExceptional_dimension D B s hs) U _ (sectionExceptional_complement_mapsTo D B s hs U)
    (2 * (Geometric.DimensionCycles.dimensionCodimension V D.val + 1)) (by omega)

 theorem section_relativeRestriction_injective (U : Opens V.analyticSpace) :
    Function.Injective (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      {x : U | V.analyticUnderlying x.val ∈ sectionExceptional D B s hs}ᶜ
      {x : U | V.analyticUnderlying x.val ∈ ClosedSupport.Constructions.sectionClosedSupport D B s}ᶜ
      (2 * (Geometric.DimensionCycles.dimensionCodimension V D.val + 1))) := by
  let := section_relativeRestriction_isIso D B s hs U
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

 theorem retained_supportPoint_good (x : V.analyticSpace)
    (hx : V.analyticUnderlying x ∈ ClosedSupport.Constructions.sectionClosedSupport D B s)
    (he : V.analyticUnderlying x ∉ sectionExceptional D B s hs) :
    x ∈ Normalization.PrincipalZero.Constructions.BoundaryUnion.commonOpen V D.val (Affine.SectionFunction.Constructions.parentSectionFunction D B s) hs :=
  fun hbad => he ⟨hbad, hx⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Section.BoundaryRemoval.Constructions
