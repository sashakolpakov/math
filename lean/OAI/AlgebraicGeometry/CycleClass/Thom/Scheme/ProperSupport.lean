import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.ResidueDegree

/-! # Proper Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

noncomputable section

/-! Genuine reduced support images for proper maps of general complex
schemes, without projectivity or smoothness assumptions on the source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsProper f.left]
  (Z : IrreducibleCloseds X.left)

/-- The actual reduced closure of the image of the original reduced support. -/
def imageSupport : IrreducibleCloseds Y.left :=
  Geometric.StratumClosure.integralImageClosure (Geometric.GenericPoint.reducedSupportι Z ≫ f.left)

theorem imageSupport_eq_image :
    (imageSupport f Z : Set Y.left) = f.left '' (Z : Set X.left) := by
  change closure (Set.range (Geometric.GenericPoint.reducedSupportι Z ≫ f.left)) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Geometric.GenericPoint.range_reducedSupportι]
  exact (f.left.isClosedMap _ Z.isClosed).closure_eq

/-- The original map factors through its actual reduced image. -/
def imageMap : Geometric.GenericPoint.reducedSupportScheme Z ⟶ Geometric.GenericPoint.reducedSupportScheme (imageSupport f Z) :=
  Geometric.StratumClosure.toReducedImageClosure (Geometric.GenericPoint.reducedSupportι Z ≫ f.left)

theorem imageMap_inclusion :
    imageMap f Z ≫ Geometric.GenericPoint.reducedSupportι (imageSupport f Z) = Geometric.GenericPoint.reducedSupportι Z ≫ f.left :=
  Geometric.StratumClosure.toReducedImageClosure_inclusion _

theorem imageMap_over :
    imageMap f Z ≫ Geometric.SupportFiniteType.supportStructureMap (imageSupport f Z) Y.hom = Geometric.SupportFiniteType.supportStructureMap Z X.hom := by
  change imageMap f Z ≫ Geometric.GenericPoint.reducedSupportι (imageSupport f Z) ≫ Y.hom = Geometric.GenericPoint.reducedSupportι Z ≫ X.hom
  rw [← Category.assoc, imageMap_inclusion, Category.assoc, f.w]

def imageOverMap : RegularSupport.Constructions.supportOver X Z ⟶ RegularSupport.Constructions.supportOver Y (imageSupport f Z) :=
  Over.homMk (imageMap f Z) (imageMap_over f Z)

theorem imageOverMap_inclusion :
    imageOverMap f Z ≫ RegularSupport.Constructions.supportToAmbient Y (imageSupport f Z) = RegularSupport.Constructions.supportToAmbient X Z ≫ f := by
  apply Over.OverMorphism.ext
  exact imageMap_inclusion f Z

instance imageMap_proper : IsProper (imageMap f Z) := by
  let : IsProper (imageMap f Z ≫ Geometric.GenericPoint.reducedSupportι (imageSupport f Z)) := by
    rw [imageMap_inclusion]
    infer_instance
  exact IsProper.of_comp (imageMap f Z) (Geometric.GenericPoint.reducedSupportι (imageSupport f Z))

theorem imageMap_finite [IsFinite f.left] : IsFinite (imageMap f Z) := by
  let : IsFinite (imageMap f Z ≫ Geometric.GenericPoint.reducedSupportι (imageSupport f Z)) := by
    rw [imageMap_inclusion]
    infer_instance
  exact IsFinite.of_comp (imageMap f Z) (Geometric.GenericPoint.reducedSupportι (imageSupport f Z))

theorem imageMap_surjective : Function.Surjective (imageMap f Z) := by
  intro y
  have hy : Geometric.GenericPoint.reducedSupportι (imageSupport f Z) y ∈ (imageSupport f Z : Set Y.left) := by
    rw [← Geometric.GenericPoint.range_reducedSupportι]
    exact Set.mem_range_self y
  rw [imageSupport_eq_image] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [← Geometric.GenericPoint.range_reducedSupportι Z] at hx
  obtain ⟨z, rfl⟩ := hx
  refine ⟨z, (Geometric.GenericPoint.reducedSupportι (imageSupport f Z)).isClosedEmbedding.injective ?_⟩
  exact (congrArg (fun i : Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y.left => i z)
    (imageMap_inclusion f Z)).trans hxy

theorem imageMap_genericPoint :
    imageMap f Z (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z)) =
      genericPoint (Geometric.GenericPoint.reducedSupportScheme (imageSupport f Z)) :=
  ProperImage.SupportMap.Constructions.Construction.genericPoint_eq_of_surjective _ (imageMap_surjective f Z)

/-- Factoring through the reduced supports retains exactly the original
residue-field degree at the source support's actual generic point. -/
theorem imageMap_residueDegree :
    (imageMap f Z).residueDegree (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z)) =
      f.left.residueDegree (irreducibleSetEquivPoints Z) := by
  have h := congrArg
    (fun i : Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y.left => i.residueDegree (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z)))
    (imageMap_inclusion f Z)
  rw [ProperImage.ResidueDegree.Constructions.Construction.residueDegree_post_immersion,
    ProperImage.ResidueDegree.Constructions.Construction.residueDegree_pre_immersion, Geometric.GenericPoint.reducedSupport_genericPoint_eq] at h
  exact h

theorem imageSupport_genericPoint :
    irreducibleSetEquivPoints (imageSupport f Z) = f.left (irreducibleSetEquivPoints Z) := by
  have h := congrArg (fun i : Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y.left =>
    i (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z))) (imageMap_inclusion f Z)
  change Geometric.GenericPoint.reducedSupportι (imageSupport f Z) (imageMap f Z (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z))) =
    f.left (Geometric.GenericPoint.reducedSupportι Z (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z))) at h
  rw [imageMap_genericPoint, Geometric.GenericPoint.reducedSupport_genericPoint_eq, Geometric.GenericPoint.reducedSupport_genericPoint_eq] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
