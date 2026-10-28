import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo

/-! # Open Support Closure -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure

noncomputable section

/-! An actual reduced closed support in an ambient open is an open
subscheme of its reduced closure in the full ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) [IsOpenImmersion i.left] [QuasiCompact i.left]
  (Z : IrreducibleCloseds X.left)

def closureSupport : IrreducibleCloseds Y.left :=
  Geometric.StratumClosure.integralImageClosure (Geometric.GenericPoint.reducedSupportι Z ≫ i.left)

omit [IsOpenImmersion i.left] [QuasiCompact i.left] in
theorem closureSupport_coe :
    (closureSupport i Z : Set Y.left) = closure (i.left '' (Z : Set X.left)) := by
  change closure (Set.range (Geometric.GenericPoint.reducedSupportι Z ≫ i.left)) = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Geometric.GenericPoint.range_reducedSupportι]

def toClosure : Geometric.GenericPoint.reducedSupportScheme Z ⟶ Geometric.GenericPoint.reducedSupportScheme (closureSupport i Z) :=
  Geometric.StratumClosure.toReducedImageClosure (Geometric.GenericPoint.reducedSupportι Z ≫ i.left)

instance toClosure_open : IsOpenImmersion (toClosure i Z) :=
  inferInstanceAs (IsOpenImmersion (Geometric.StratumClosure.toReducedImageClosure (Geometric.GenericPoint.reducedSupportι Z ≫ i.left)))

omit [IsOpenImmersion i.left] in
theorem toClosure_inclusion :
    toClosure i Z ≫ Geometric.GenericPoint.reducedSupportι (closureSupport i Z) = Geometric.GenericPoint.reducedSupportι Z ≫ i.left :=
  Geometric.StratumClosure.toReducedImageClosure_inclusion _

omit [IsOpenImmersion i.left] in
theorem toClosure_over :
    toClosure i Z ≫ Geometric.SupportFiniteType.supportStructureMap (closureSupport i Z) Y.hom = Geometric.SupportFiniteType.supportStructureMap Z X.hom := by
  change toClosure i Z ≫ Geometric.GenericPoint.reducedSupportι (closureSupport i Z) ≫ Y.hom = _
  rw [← Category.assoc, toClosure_inclusion, Category.assoc, i.w]
  rfl

def toClosureOver : RegularSupport.Constructions.supportOver X Z ⟶ RegularSupport.Constructions.supportOver Y (closureSupport i Z) :=
  Over.homMk (toClosure i Z) (toClosure_over i Z)

omit [IsOpenImmersion i.left] in
theorem toClosureOver_ambient :
    toClosureOver i Z ≫ RegularSupport.Constructions.supportToAmbient Y (closureSupport i Z) = RegularSupport.Constructions.supportToAmbient X Z ≫ i := by
  apply Over.OverMorphism.ext
  exact toClosure_inclusion i Z

theorem closureSupport_dimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (closureSupport i Z) Y.hom = Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom := by
  have h := Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (Geometric.GenericPoint.reducedSupportι Z ≫ i.left) Y.hom
  rw [Category.assoc, i.w] at h
  exact h.symm

theorem closureSupport_genericPoint :
    irreducibleSetEquivPoints (closureSupport i Z) = i.left (irreducibleSetEquivPoints Z) := by
  have h := congrArg (fun f : Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y.left => f (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z)))
    (toClosure_inclusion i Z)
  change Geometric.GenericPoint.reducedSupportι (closureSupport i Z) (toClosure i Z (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z))) =
    i.left (Geometric.GenericPoint.reducedSupportι Z (genericPoint (Geometric.GenericPoint.reducedSupportScheme Z))) at h
  rw [genericPoint_eq_of_isOpenImmersion, Geometric.GenericPoint.reducedSupport_genericPoint_eq, Geometric.GenericPoint.reducedSupport_genericPoint_eq] at h
  exact h

omit [QuasiCompact i.left] in
theorem closureSupport_preimage : i.left ⁻¹' (closureSupport i Z : Set Y.left) = (Z : Set X.left) := by
  rw [closureSupport_coe]
  exact i.left.isOpenEmbedding.isOpenMap.preimage_closure_image
    i.left.isOpenEmbedding.injective i.left.continuous (Z : Set X.left) Z.isClosed

variable [LocallyOfFiniteType Y.hom]

/-- Any actual smooth open immersion into a support factors through its
canonical regular locus by an actual open immersion. -/
def smoothOpenToRegular {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom]
    (W : IrreducibleCloseds Y.left) (j : S ⟶ RegularSupport.Constructions.supportOver Y W) [IsOpenImmersion j.left] :
    S ⟶ RegularSupport.Constructions.regularOver Y W := by
  have hj : j.left ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom = S.hom := j.w
  let : Smooth (j.left ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom) := by rw [hj]; infer_instance
  refine Over.homMk (Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift j.left (Geometric.SupportFiniteType.supportStructureMap W Y.hom)) ?_
  change Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift j.left (Geometric.SupportFiniteType.supportStructureMap W Y.hom) ≫
    Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap W Y.hom) ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom = S.hom
  rw [← Category.assoc, Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift_inclusion]
  exact hj

instance smoothOpenToRegular_open {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom]
    (W : IrreducibleCloseds Y.left) (j : S ⟶ RegularSupport.Constructions.supportOver Y W) [IsOpenImmersion j.left] :
    IsOpenImmersion (smoothOpenToRegular W j).left := by
  have hj : j.left ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom = S.hom := j.w
  let : Smooth (j.left ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom) := by rw [hj]; infer_instance
  change IsOpenImmersion (Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift j.left (Geometric.SupportFiniteType.supportStructureMap W Y.hom))
  infer_instance

theorem smoothOpenToRegular_inclusion {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom]
    (W : IrreducibleCloseds Y.left) (j : S ⟶ RegularSupport.Constructions.supportOver Y W) [IsOpenImmersion j.left] :
    smoothOpenToRegular W j ≫ SmoothSupportOpen.Constructions.regularToSupport Y W = j := by
  have hj : j.left ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom = S.hom := j.w
  let : Smooth (j.left ≫ Geometric.SupportFiniteType.supportStructureMap W Y.hom) := by rw [hj]; infer_instance
  apply Over.OverMorphism.ext
  exact Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift_inclusion j.left (Geometric.SupportFiniteType.supportStructureMap W Y.hom)

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.OpenSupportClosure
