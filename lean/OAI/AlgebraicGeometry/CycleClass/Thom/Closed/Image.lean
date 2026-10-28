import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SupportMap
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ResidueDegree

/-! # Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Image

noncomputable section

/-! A closed immersion sends each actual support to its reduced image
with multiplicity one and preserves its dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Reduction.Constructions

variable {V X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : V.toOver ⟶ X.toOver) [IsClosedImmersion f.left]

instance supportImageMap_isIso {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    IsIso (ProperImage.SupportMap.Constructions.Construction.supportImageMap f (show IsProper f.left from inferInstance) Z) := by
  let : IsClosedImmersion (ProperImage.SupportMap.Constructions.Construction.algebraicMap f) := inferInstanceAs (IsClosedImmersion f.left)
  apply IsClosedImmersion.isIso_lift
  change (Geometric.GenericPoint.reducedSupportIdeal (ProperImage.Reduction.Constructions.imageSupport f Z)).subschemeι.ker = (Z.inclusion ≫ ProperImage.SupportMap.Constructions.Construction.algebraicMap f).ker
  rw [Scheme.IdealSheafData.ker_subschemeι,
    ProperImage.SupportMap.Constructions.Construction.supportMap_kernel f (show IsProper f.left from inferInstance) Z]

theorem closedImage_supportDimension {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperImage.Reduction.Constructions.imageSupport f Z) X.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.val V.structureMap := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (ProperImage.SupportMap.Constructions.Construction.supportImageMap f (show IsProper f.left from inferInstance) Z)
    (Geometric.SupportFiniteType.supportStructureMap (ProperImage.Reduction.Constructions.imageSupport f Z) X.structureMap)
  rw [ProperImage.SupportMap.Constructions.Construction.supportImageMap_over] at h
  exact h.symm

theorem closedImage_residueDegree (x : V.carrier) : f.left.residueDegree x = 1 := by
  have h := ProperImage.ResidueDegree.Constructions.Construction.residueDegree_post_immersion (𝟙 V.carrier) f.left x
  simpa only [Category.id_comp, Scheme.Hom.residueDegree_id] using h

variable (p q : ℕ) (hdeg : p + X.complexDimension = q + V.complexDimension)

def closedImageCycleSupport (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) : Geometric.DimensionCycles.DimensionCycleSupport X q :=
  ⟨ProperImage.Reduction.Constructions.imageSupport f Z, ProperImage.Reduction.Constructions.imageCodimension_eq f p q hdeg Z (closedImage_supportDimension f Z)⟩

theorem closedImageCycleSupport_genericPoint (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (closedImageCycleSupport f p q hdeg Z).genericPoint = f.left Z.genericPoint :=
  irreducibleSetEquivPoints.apply_symm_apply _

theorem closedImageCycleSupport_injective : Function.Injective (closedImageCycleSupport f p q hdeg) := by
  intro A B he
  apply Geometric.DimensionCycles.DimensionCycleSupport.genericPoint_injective
  apply f.left.isClosedEmbedding.injective
  have h := congrArg Geometric.DimensionCycles.DimensionCycleSupport.genericPoint he
  rw [closedImageCycleSupport_genericPoint, closedImageCycleSupport_genericPoint] at h
  exact h

theorem cyclePushforwardGenerator_closed (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ProperImage.Reduction.Constructions.cyclePushforwardGenerator f p q hdeg Z = Finsupp.single (closedImageCycleSupport f p q hdeg Z) 1 := by
  rw [ProperImage.Reduction.Constructions.cyclePushforwardGenerator_of_dimension_eq f p q hdeg Z (closedImage_supportDimension f Z),
    closedImage_residueDegree, Nat.cast_one]
  rfl

theorem cyclePushforward_closed (z : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    ProperImage.Reduction.Constructions.cyclePushforward f (show IsProper f.left from inferInstance) p q hdeg z =
      Finsupp.mapDomain (closedImageCycleSupport f p q hdeg) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add a b ha hb => rw [map_add, ha, hb, Finsupp.mapDomain_add]
  | single Z r =>
      rw [ProperImage.Reduction.Constructions.cyclePushforward_single, cyclePushforwardGenerator_closed, Finsupp.smul_single,
        smul_eq_mul, mul_one, Finsupp.mapDomain_single]

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Image
