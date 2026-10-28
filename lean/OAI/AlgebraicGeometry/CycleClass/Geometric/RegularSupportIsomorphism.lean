import OAI.AlgebraicGeometry.CycleClass.Geometric.IrreducibleSupportIsomorphism
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying

/-! # Regular Support Isomorphism -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism

noncomputable section

/-!
# Actual reduced supports and smooth strata under isomorphisms

The reduced support is transported by equality of its actual kernel ideal
sheaf. Its smooth locus is transported by the native smooth-locus preimage
theorem. All isomorphisms commute with the genuine inclusions and structure
maps. The singular boundary is the actual image of the complementary locus.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y S : Scheme.{u}}

/-- The reduced support followed by the given ambient scheme isomorphism. -/
def reducedSupportIsoMap (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    GenericPoint.reducedSupportScheme Z ⟶ Y := GenericPoint.reducedSupportι Z ≫ e.hom

instance reducedSupportIsoMap_isClosedImmersion (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    IsClosedImmersion (reducedSupportIsoMap e Z) := by
  unfold reducedSupportIsoMap
  infer_instance

theorem reducedSupportIsoMap_range (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    Set.range (reducedSupportIsoMap e Z) = (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z : Set Y) := by
  change Set.range (e.hom ∘ GenericPoint.reducedSupportι Z) = _
  rw [Set.range_comp, GenericPoint.range_reducedSupportι]
  rfl

theorem reducedSupportIsoMap_imageClosure (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    StratumClosure.integralImageClosure (reducedSupportIsoMap e Z) = IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (reducedSupportIsoMap e Z)) = _
  rw [reducedSupportIsoMap_range, (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z).isClosed.closure_eq]

/-- Equality of ideal sheaves, not just equality of underlying closed sets. -/
theorem reducedSupportIsoMap_kernel (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    (reducedSupportIsoMap e Z).ker = GenericPoint.reducedSupportIdeal (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) := by
  rw [StratumClosure.kernel_eq_reducedImageClosureIdeal, reducedSupportIsoMap_imageClosure]

/-- The actual reduced support schemes are canonically isomorphic. -/
def reducedSupportSchemeIso (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    GenericPoint.reducedSupportScheme Z ≅ GenericPoint.reducedSupportScheme (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) := by
  have hk : (GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z)).ker =
      (reducedSupportIsoMap e Z).ker := by
    change (GenericPoint.reducedSupportIdeal (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z)).subschemeι.ker = _
    rw [Scheme.IdealSheafData.ker_subschemeι, reducedSupportIsoMap_kernel]
  let f := IsClosedImmersion.lift (GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z))
    (reducedSupportIsoMap e Z) hk.le
  let : IsIso f := IsClosedImmersion.isIso_lift
    (GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z)) (reducedSupportIsoMap e Z) hk
  exact asIso f

@[reassoc]
theorem reducedSupportSchemeIso_hom_inclusion (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    (reducedSupportSchemeIso e Z).hom ≫ GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) =
      GenericPoint.reducedSupportι Z ≫ e.hom := by
  change IsClosedImmersion.lift _ _ _ ≫ _ = _
  exact IsClosedImmersion.lift_fac _ _ _

@[reassoc]
theorem reducedSupportSchemeIso_inv_inclusion (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    (reducedSupportSchemeIso e Z).inv ≫ GenericPoint.reducedSupportι Z =
      GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) ≫ e.inv := by
  apply (cancel_epi (reducedSupportSchemeIso e Z).hom).mp
  simp only [Iso.hom_inv_id_assoc, reducedSupportSchemeIso_hom_inclusion_assoc,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc]
theorem reducedSupportSchemeIso_over (e : X ≅ Y) (Z : IrreducibleCloseds X)
    (f : X ⟶ S) (g : Y ⟶ S) (h : e.hom ≫ g = f) :
    (reducedSupportSchemeIso e Z).hom ≫
        SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g = SupportFiniteType.supportStructureMap Z f := by
  unfold SupportFiniteType.supportStructureMap
  rw [reducedSupportSchemeIso_hom_inclusion_assoc, h]

/-- The support isomorphism preserves the actual structure morphism. -/
def reducedSupportOverIso (e : X ≅ Y) (Z : IrreducibleCloseds X)
    (f : X ⟶ S) (g : Y ⟶ S) (h : e.hom ≫ g = f) :
    Over.mk (SupportFiniteType.supportStructureMap Z f) ≅
      Over.mk (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g) :=
  Over.isoMk (reducedSupportSchemeIso e Z) (reducedSupportSchemeIso_over e Z f g h)

section SmoothLocus

variable (e : X ≅ Y) (f : X ⟶ S) (g : Y ⟶ S)
variable [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
variable (h : e.hom ≫ g = f)
include h

/-- Smoothness is transported along the actual source isomorphism. -/
theorem smoothLocus_preimage_of_iso : e.hom ⁻¹ᵁ g.smoothLocus = f.smoothLocus := by
  subst f
  exact Scheme.Hom.preimage_smoothLocus_eq e.hom g

/-- Restriction of the actual scheme isomorphism to the actual smooth loci. -/
def smoothStratumIso : SmoothStratum.smoothStratum f ≅ SmoothStratum.smoothStratum g :=
  X.isoOfEq (smoothLocus_preimage_of_iso e f g h).symm ≪≫
    e.hom.preimageIso g.smoothLocus

@[reassoc]
theorem smoothStratumIso_hom_inclusion :
    (smoothStratumIso e f g h).hom ≫ SmoothStratum.smoothStratumι g = SmoothStratum.smoothStratumι f ≫ e.hom := by
  dsimp only [smoothStratumIso, Iso.trans_hom, SmoothStratum.smoothStratumι]
  rw [Category.assoc, Scheme.Hom.preimageIso_hom_ι,
    Scheme.isoOfEq_hom_ι_assoc]

@[reassoc]
theorem smoothStratumIso_over :
    (smoothStratumIso e f g h).hom ≫ SmoothStratum.smoothStratumToBase g = SmoothStratum.smoothStratumToBase f := by
  unfold SmoothStratum.smoothStratumToBase
  rw [smoothStratumIso_hom_inclusion_assoc, h]

def smoothStratumOverIso : Over.mk (SmoothStratum.smoothStratumToBase f) ≅
    Over.mk (SmoothStratum.smoothStratumToBase g) :=
  Over.isoMk (smoothStratumIso e f g h) (smoothStratumIso_over e f g h)

theorem singularLocus_preimage_of_iso :
    e.hom ⁻¹' SingularLocus.singularLocus g = SingularLocus.singularLocus f := by
  change (e.hom ⁻¹' (g.smoothLocus : Set Y))ᶜ = (f.smoothLocus : Set X)ᶜ
  exact congrArg (fun A : Set X => Aᶜ)
    (congrArg (fun U : X.Opens => (U : Set X)) (smoothLocus_preimage_of_iso e f g h))

theorem singularLocus_image_of_iso :
    e.hom '' SingularLocus.singularLocus f = SingularLocus.singularLocus g := by
  rw [← singularLocus_preimage_of_iso e f g h]
  exact Set.image_preimage_eq _ (Scheme.homeoOfIso e).surjective

end SmoothLocus

/-- The actual support image pulls back to exactly the original support. -/
theorem irreducibleSupportIsoEquiv_preimage (e : X ≅ Y) (Z : IrreducibleCloseds X) :
    e.hom ⁻¹' (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z : Set Y) = (Z : Set X) := by
  rw [IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv_coe]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso e).injective

section Field

variable {K : Type u} [Field K]
variable (e : X ≅ Y) (Z : IrreducibleCloseds X)
variable (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
variable [LocallyOfFiniteType f] [LocallyOfFiniteType g]
variable (h : e.hom ≫ g = f)

/-- The actual regular loci of corresponding reduced supports are isomorphic. -/
def regularSupportSchemeIso :
    SmoothStratum.smoothStratum (SupportFiniteType.supportStructureMap Z f) ≅
      SmoothStratum.smoothStratum (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g) :=
  smoothStratumIso (reducedSupportSchemeIso e Z)
    (SupportFiniteType.supportStructureMap Z f) (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g)
    (reducedSupportSchemeIso_over e Z f g h)

@[reassoc]
theorem regularSupportSchemeIso_hom_inclusion :
    (regularSupportSchemeIso e Z f g h).hom ≫
        SmoothStratum.reducedSupportSmoothStratumι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z)
          (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g) =
      SmoothStratum.reducedSupportSmoothStratumι Z (SupportFiniteType.supportStructureMap Z f) ≫ e.hom := by
  dsimp only [regularSupportSchemeIso, SmoothStratum.reducedSupportSmoothStratumι]
  rw [smoothStratumIso_hom_inclusion_assoc, reducedSupportSchemeIso_hom_inclusion]
  rw [Category.assoc]

@[reassoc]
theorem regularSupportSchemeIso_over :
    (regularSupportSchemeIso e Z f g h).hom ≫
        SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g) =
      SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap Z f) :=
  smoothStratumIso_over (reducedSupportSchemeIso e Z)
    (SupportFiniteType.supportStructureMap Z f) (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g)
    (reducedSupportSchemeIso_over e Z f g h)

/-- The regular-support isomorphism is an actual isomorphism over the field. -/
def regularSupportOverIso :
    Over.mk (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap Z f)) ≅
      Over.mk (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g)) :=
  Over.isoMk (regularSupportSchemeIso e Z f g h) (regularSupportSchemeIso_over e Z f g h)

include h in
/-- The actual singular boundary is carried exactly to the singular boundary
of the corresponding support. -/
theorem supportSingularBoundary_image_of_iso :
    e.hom '' StratumDimension.supportSingularBoundary Z f =
      StratumDimension.supportSingularBoundary (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g := by
  have hs := singularLocus_image_of_iso (reducedSupportSchemeIso e Z)
    (SupportFiniteType.supportStructureMap Z f) (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g)
    (reducedSupportSchemeIso_over e Z f g h)
  calc
    e.hom '' StratumDimension.supportSingularBoundary Z f =
        (GenericPoint.reducedSupportι Z ≫ e.hom) '' SingularLocus.singularLocus (SupportFiniteType.supportStructureMap Z f) := by
      unfold StratumDimension.supportSingularBoundary
      rw [Set.image_image]
      rfl
    _ = ((reducedSupportSchemeIso e Z).hom ≫
        GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z)) ''
          SingularLocus.singularLocus (SupportFiniteType.supportStructureMap Z f) := by
      rw [reducedSupportSchemeIso_hom_inclusion]
    _ = (GenericPoint.reducedSupportι (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z)) ''
        ((reducedSupportSchemeIso e Z).hom '' SingularLocus.singularLocus (SupportFiniteType.supportStructureMap Z f)) := by
      rw [Set.image_image]
      rfl
    _ = StratumDimension.supportSingularBoundary (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g := by
      rw [hs]
      rfl

include h in
theorem supportSingularBoundary_preimage_of_iso :
    e.hom ⁻¹' StratumDimension.supportSingularBoundary (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g =
      StratumDimension.supportSingularBoundary Z f := by
  rw [← supportSingularBoundary_image_of_iso e Z f g h]
  exact Set.preimage_image_eq _ (Scheme.homeoOfIso e).injective

include h in
/-- Over a perfect field the integral regular loci retain their actual
function-field dimensions under this isomorphism. -/
theorem regularSupportSchemeIso_transcendenceDimension [PerfectField K] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
        (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g)) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap Z f)) := by
  have hd := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (regularSupportSchemeIso e Z f g h).hom
    (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv e Z) g))
  rw [regularSupportSchemeIso_over] at hd
  exact hd.symm

end Field

variable {V W : Over Foundations.Scheme.ProjectiveSpace.complexBase} (e : V ≅ W) (Z : IrreducibleCloseds V.left)

/-- On ordinary complex points the actual transported support pulls back
exactly to the original support. -/
theorem complexPoints_preimage_supportIso :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹'
          (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv (X := V.left) (Y := W.left)
            ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) Z : Set W.left)) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (Z : Set V.left) := by
  ext x
  change e.hom.left (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x) ∈
      e.hom.left '' (Z : Set V.left) ↔ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ (Z : Set V.left)
  have hi : Function.Injective e.hom.left :=
    (Scheme.homeoOfIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e)).injective
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact hi hxy ▸ hy
  · intro hx
    exact ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, hx, rfl⟩

variable [LocallyOfFiniteType V.hom] [LocallyOfFiniteType W.hom]

/-- The corresponding exact singular-boundary identity for ordinary complex
points. Taking complements gives the maps of pairs used in relative cohomology. -/
theorem complexPoints_preimage_singularBoundaryIso :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹'
          StratumDimension.supportSingularBoundary (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv
            ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) Z) W.hom) =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' StratumDimension.supportSingularBoundary Z V.hom := by
  ext x
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈
      (((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).hom ⁻¹'
        StratumDimension.supportSingularBoundary (IrreducibleSupportIsomorphism.irreducibleSupportIsoEquiv
          ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) Z) W.hom) ↔ _
  rw [supportSingularBoundary_preimage_of_iso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e)
    Z V.hom W.hom e.hom.w]
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism
