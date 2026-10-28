import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure
import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField

/-! # Projective Component Dimension -/

namespace OAI.AlgebraicGeometry

noncomputable section

section

/-!
# Irreducible supports in the actual integral components

Every irreducible closed support of a smooth projective presentation lies in
one of its genuine open and closed integral components. Image and preimage
under those component inclusions give the support decomposition below.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace Set

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- A nonempty support cannot lie in two distinct actual components. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.component_eq_of_support_subset (Z : IrreducibleCloseds P.carrier)
    (C D : irreducibleComponents P.carrier)
    (hC : (Z : Set P.carrier) ⊆ C.val) (hD : (Z : Set P.carrier) ⊆ D.val) : C = D := by
  obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
  let := P.stalk_isDomain x
  apply Subtype.ext
  exact Foundations.Scheme.LocalDomainComponents.irreducibleComponents_eq_of_mem_of_stalkDomain x C.property D.property (hC hx) (hD hx)

/-- Every irreducible closed support lies in a unique integral component. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.support_existsUnique_component (Z : IrreducibleCloseds P.carrier) :
    ∃! C : irreducibleComponents P.carrier, (Z : Set P.carrier) ⊆ C.val := by
  obtain ⟨C, hC, hZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (Z : Set P.carrier) Z.isIrreducible
  refine ⟨⟨C, hC⟩, hZ, ?_⟩
  intro D hD
  exact P.component_eq_of_support_subset Z D ⟨C, hC⟩ hD hZ

/-- The unique actual component containing the support. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportComponent (Z : IrreducibleCloseds P.carrier) : irreducibleComponents P.carrier :=
  Classical.choose (P.support_existsUnique_component Z).exists

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.support_subset_component (Z : IrreducibleCloseds P.carrier) :
    (Z : Set P.carrier) ⊆ (P.supportComponent Z).val :=
  Classical.choose_spec (P.support_existsUnique_component Z).exists

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportComponent_eq_of_subset (Z : IrreducibleCloseds P.carrier)
    (C : irreducibleComponents P.carrier) (hC : (Z : Set P.carrier) ⊆ C.val) :
    P.supportComponent Z = C :=
  P.component_eq_of_support_subset Z (P.supportComponent Z) C (P.support_subset_component Z) hC

/-- Image of an irreducible closed support under the actual component inclusion.
The image is closed because the component inclusion is a closed immersion. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) : IrreducibleCloseds P.carrier :=
  ⟨P.componentInclusion C '' (Z : Set (P.componentVariety C).carrier),
    Z.isIrreducible.image _ (P.componentInclusion C).continuous.continuousOn,
    (P.componentInclusion C).isClosedEmbedding.isClosedMap _ Z.isClosed⟩

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_coe (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    (P.componentSupportImage C Z : Set P.carrier) =
      P.componentInclusion C '' (Z : Set (P.componentVariety C).carrier) := rfl

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_subset (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    (P.componentSupportImage C Z : Set P.carrier) ⊆ C.val := by
  rw [← P.componentInclusion_range C]
  exact Set.image_subset_range _ _

/-- Restriction of a support contained in a component is its actual preimage. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportPreimage (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds P.carrier) (hZ : (Z : Set P.carrier) ⊆ C.val) :
    IrreducibleCloseds (P.componentVariety C).carrier := by
  refine ⟨P.componentInclusion C ⁻¹' (Z : Set P.carrier), ?_,
    Z.isClosed.preimage (P.componentInclusion C).continuous⟩
  apply Z.isIrreducible.preimage (P.componentInclusion C).isOpenEmbedding
  obtain ⟨x, hx⟩ := Z.isIrreducible.nonempty
  refine ⟨x, hx, ?_⟩
  rw [P.componentInclusion_range C]
  exact hZ hx

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportPreimage_coe (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds P.carrier) (hZ : (Z : Set P.carrier) ⊆ C.val) :
    (P.componentSupportPreimage C Z hZ : Set (P.componentVariety C).carrier) =
      P.componentInclusion C ⁻¹' (Z : Set P.carrier) := rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_preimage (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds P.carrier) (hZ : (Z : Set P.carrier) ⊆ C.val) :
    P.componentSupportImage C (P.componentSupportPreimage C Z hZ) = Z := by
  apply IrreducibleCloseds.ext
  apply Set.image_preimage_eq_of_subset
  rwa [P.componentInclusion_range C]

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportPreimage_image (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    P.componentSupportPreimage C (P.componentSupportImage C Z)
      (P.componentSupportImage_subset C Z) = Z := by
  apply IrreducibleCloseds.ext
  exact Set.preimage_image_eq _ (P.componentInclusion C).isOpenEmbedding.injective

theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_injective (C : irreducibleComponents P.carrier) :
    Function.Injective (P.componentSupportImage C) := by
  intro Z W h
  apply IrreducibleCloseds.ext
  apply (Set.image_eq_image (P.componentInclusion C).isOpenEmbedding.injective).mp
  exact congrArg (fun T : IrreducibleCloseds P.carrier => (T : Set P.carrier)) h

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportComponent_image (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    P.supportComponent (P.componentSupportImage C Z) = C :=
  P.supportComponent_eq_of_subset _ C (P.componentSupportImage_subset C Z)

/-- Taking the image of a support remembers its unique component as well. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_sigma_injective :
    Function.Injective (fun Z : Σ C : irreducibleComponents P.carrier,
      IrreducibleCloseds (P.componentVariety C).carrier => P.componentSupportImage Z.1 Z.2) := by
  rintro ⟨C, Z⟩ ⟨D, W⟩ h
  change P.componentSupportImage C Z = P.componentSupportImage D W at h
  have hCD : C = D := by
    apply P.component_eq_of_support_subset (P.componentSupportImage C Z) C D
      (P.componentSupportImage_subset C Z)
    rw [h]
    exact P.componentSupportImage_subset D W
  subst D
  have hZW : Z = W := P.componentSupportImage_injective C h
  subst W
  rfl

/-- Every support is the image of its actual preimage in its containing component. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_sigma_surjective :
    Function.Surjective (fun Z : Σ C : irreducibleComponents P.carrier,
      IrreducibleCloseds (P.componentVariety C).carrier => P.componentSupportImage Z.1 Z.2) := by
  intro Z
  refine ⟨⟨P.supportComponent Z,
    P.componentSupportPreimage (P.supportComponent Z) Z (P.support_subset_component Z)⟩, ?_⟩
  exact P.componentSupportImage_preimage (P.supportComponent Z) Z (P.support_subset_component Z)

/-- The actual decomposition of all irreducible closed supports into the
supports of the integral components, including disconnected and empty schemes. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportEquiv :
    IrreducibleCloseds P.carrier ≃
      Σ C : irreducibleComponents P.carrier, IrreducibleCloseds (P.componentVariety C).carrier :=
  (Equiv.ofBijective
    (fun Z : Σ C : irreducibleComponents P.carrier,
      IrreducibleCloseds (P.componentVariety C).carrier => P.componentSupportImage Z.1 Z.2)
    ⟨P.componentSupportImage_sigma_injective, P.componentSupportImage_sigma_surjective⟩).symm

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportEquiv_symm_apply (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    P.componentSupportEquiv.symm ⟨C, Z⟩ = P.componentSupportImage C Z := rfl

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportEquiv_image (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    P.componentSupportEquiv (P.componentSupportImage C Z) = ⟨C, Z⟩ :=
  P.componentSupportEquiv.apply_symm_apply ⟨C, Z⟩

/-- The forward equivalence is the actual preimage in any component known
to contain the support; uniqueness makes this independent of the proof. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportEquiv_apply_of_subset (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds P.carrier) (hZ : (Z : Set P.carrier) ⊆ C.val) :
    P.componentSupportEquiv Z = ⟨C, P.componentSupportPreimage C Z hZ⟩ := by
  calc
    P.componentSupportEquiv Z = P.componentSupportEquiv
        (P.componentSupportImage C (P.componentSupportPreimage C Z hZ)) :=
      congrArg P.componentSupportEquiv (P.componentSupportImage_preimage C Z hZ).symm
    _ = _ := P.componentSupportEquiv_image C _

/-- The component support has the same generic point, carried by the actual
open-and-closed immersion into the original scheme. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_genericPoint (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    irreducibleSetEquivPoints (P.componentSupportImage C Z) =
      P.componentInclusion C (irreducibleSetEquivPoints Z) := by
  have hc : IsClosed (P.componentInclusion C '' (Z : Set (P.componentVariety C).carrier)) :=
    (P.componentSupportImage C Z).isClosed
  have h : IsGenericPoint (P.componentInclusion C (irreducibleSetEquivPoints Z))
      (P.componentSupportImage C Z : Set P.carrier) := by
    change IsGenericPoint (P.componentInclusion C Z.isIrreducible.genericPoint)
      (P.componentInclusion C '' (Z : Set (P.componentVariety C).carrier))
    simpa only [hc.closure_eq] using
      (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).image
        (P.componentInclusion C).continuous
  exact (h.eq ((P.componentSupportImage C Z).isIrreducible.isGenericPoint_genericPoint
    (P.componentSupportImage C Z).isClosed)).symm

/-- Restricting an irreducible support to its component preserves its actual
codimension, measured in the specialization order. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_coheight (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    Order.coheight (P.componentSupportImage C Z) = Order.coheight Z := by
  calc
    Order.coheight (P.componentSupportImage C Z) =
        Order.coheight (irreducibleSetEquivPoints (P.componentSupportImage C Z)) :=
      (Order.coheight_orderIso irreducibleSetEquivPoints _).symm
    _ = Order.coheight (P.componentInclusion C (irreducibleSetEquivPoints Z)) := by
      rw [P.componentSupportImage_genericPoint]
    _ = Order.coheight (irreducibleSetEquivPoints Z) :=
      AlgebraicGeometry.coheight_eq_of_isOpenImmersion (P.componentInclusion C)
    _ = Order.coheight Z := Order.coheight_orderIso irreducibleSetEquivPoints Z

/-- The actual closed immersion of the reduced component support into the
original smooth projective presentation. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeMap (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ P.carrier :=
  CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ P.componentInclusion C

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeMap_isClosedImmersion (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    IsClosedImmersion (P.componentSupportSchemeMap C Z) := by
  unfold Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeMap
  infer_instance

@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeMap_range (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    Set.range (P.componentSupportSchemeMap C Z) = (P.componentSupportImage C Z : Set P.carrier) := by
  change Set.range ((P.componentInclusion C) ∘ (CycleClass.Geometric.GenericPoint.reducedSupportι Z)) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  rfl

/-- The reduced image closure is precisely the support transported from the component. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeMap_imageClosure (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (P.componentSupportSchemeMap C Z) = P.componentSupportImage C Z := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (P.componentSupportSchemeMap C Z)) = _
  rw [P.componentSupportSchemeMap_range, (P.componentSupportImage C Z).isClosed.closure_eq]

/-- Equality of the actual ideal sheaves, rather than just equality of their
topological supports, identifies the two reduced support schemes. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeMap_kernel (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    (P.componentSupportSchemeMap C Z).ker = CycleClass.Geometric.GenericPoint.reducedSupportIdeal (P.componentSupportImage C Z) := by
  rw [CycleClass.Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal, P.componentSupportSchemeMap_imageClosure]

/-- The reduced support scheme in an integral component is canonically
isomorphic to the reduced support scheme of its image in the original scheme. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeIso (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (P.componentSupportImage C Z) := by
  have hk : (CycleClass.Geometric.GenericPoint.reducedSupportι (P.componentSupportImage C Z)).ker =
      (P.componentSupportSchemeMap C Z).ker := by
    change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (P.componentSupportImage C Z)).subschemeι.ker = _
    rw [Scheme.IdealSheafData.ker_subschemeι, P.componentSupportSchemeMap_kernel]
  let f := IsClosedImmersion.lift (CycleClass.Geometric.GenericPoint.reducedSupportι (P.componentSupportImage C Z))
    (P.componentSupportSchemeMap C Z) hk.le
  letI : IsIso f := IsClosedImmersion.isIso_lift
    (CycleClass.Geometric.GenericPoint.reducedSupportι (P.componentSupportImage C Z)) (P.componentSupportSchemeMap C Z) hk
  exact asIso f

/-- The support isomorphism commutes with the actual closed immersions into
the original ambient scheme. -/
@[reassoc]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeIso_hom_inclusion (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    (P.componentSupportSchemeIso C Z).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (P.componentSupportImage C Z) =
      CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ P.componentInclusion C := by
  change IsClosedImmersion.lift _ _ _ ≫ _ = _
  exact IsClosedImmersion.lift_fac _ _ _

/-- In particular, the reduced support comparison preserves the specified
complex structure maps. -/
@[reassoc]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportSchemeIso_over (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    (P.componentSupportSchemeIso C Z).hom ≫
        CycleClass.Geometric.SupportFiniteType.supportStructureMap (P.componentSupportImage C Z) P.structureMap =
      CycleClass.Geometric.SupportFiniteType.supportStructureMap Z (P.componentVariety C).structureMap := by
  unfold CycleClass.Geometric.SupportFiniteType.supportStructureMap
  rw [P.componentSupportSchemeIso_hom_inclusion_assoc, P.componentInclusion_over]

end

/-!
# Dimension-graded supports in the integral components

The reduced support scheme and its structure morphism are preserved by the
actual component inclusion. Consequently its native transcendence dimension
is preserved as well. This identifies the codimension-graded supports of a
possibly disconnected smooth projective scheme with those of its integral
components, including components of different dimensions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- Passing from a component support to its ambient image preserves the
actual function-field transcendence dimension over the specified base. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentSupportImage_transcendenceDimension
    (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (P.componentSupportImage C Z) P.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z (P.componentVariety C).structureMap := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (P.componentSupportSchemeIso C Z).hom
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (P.componentSupportImage C Z) P.structureMap)
  rw [P.componentSupportSchemeIso_over C Z] at h
  exact h.symm

/-- Codimension is measured in the unique actual irreducible component
containing the support, so this also covers varieties of mixed dimension. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension (Z : IrreducibleCloseds P.carrier) : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.componentVariety (P.supportComponent Z)).structureMap -
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z P.structureMap

/-- This codimension restricts to the previously constructed integral
variety codimension without any change of grading. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension_componentSupportImage
    (C : irreducibleComponents P.carrier)
    (Z : IrreducibleCloseds (P.componentVariety C).carrier) :
    P.supportCodimension (P.componentSupportImage C Z) =
      CycleClass.Geometric.DimensionCycles.dimensionCodimension (P.componentVariety C) Z := by
  have hC := congrArg
    (fun D : irreducibleComponents P.carrier =>
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.componentVariety D).structureMap)
    (P.supportComponent_image C Z)
  exact congrArg₂ Nat.sub hC (P.componentSupportImage_transcendenceDimension C Z)

/-- The actual support equivalence preserves codimension in both directions. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension_componentSupportEquiv (Z : IrreducibleCloseds P.carrier) :
    P.supportCodimension Z =
      CycleClass.Geometric.DimensionCycles.dimensionCodimension (P.componentVariety (P.componentSupportEquiv Z).1)
        (P.componentSupportEquiv Z).2 := by
  obtain ⟨⟨C, W⟩, rfl⟩ := P.componentSupportEquiv.symm.surjective Z
  exact (P.supportCodimension_componentSupportImage C W).trans
    (congrArg
      (fun T : Σ D : irreducibleComponents P.carrier,
          IrreducibleCloseds (P.componentVariety D).carrier =>
        CycleClass.Geometric.DimensionCycles.dimensionCodimension (P.componentVariety T.1) T.2)
      (P.componentSupportEquiv_image C W)).symm

/-- Genuine irreducible closed supports of a specified codimension in a
smooth projective presentation, with the native component dimension. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.DimensionCycleSupport (p : ℕ) :=
  {Z : IrreducibleCloseds P.carrier // P.supportCodimension Z = p}

/-- Restricting the actual support equivalence to one codimension. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionSupportEquiv (p : ℕ) :
    P.DimensionCycleSupport p ≃
      Σ C : irreducibleComponents P.carrier,
        CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p := by
  let e :
      {T : Σ C : irreducibleComponents P.carrier,
          IrreducibleCloseds (P.componentVariety C).carrier //
        CycleClass.Geometric.DimensionCycles.dimensionCodimension (P.componentVariety T.1) T.2 = p} ≃
        Σ C : irreducibleComponents P.carrier,
          CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p :=
    { toFun := fun T => ⟨T.1.1, ⟨T.1.2, T.2⟩⟩
      invFun := fun T => ⟨⟨T.1, T.2.1⟩, T.2.2⟩
      left_inv := by rintro ⟨⟨C, Z⟩, hZ⟩; rfl
      right_inv := by rintro ⟨C, Z, hZ⟩; rfl }
  exact (P.componentSupportEquiv.subtypeEquiv
    (fun Z => by rw [P.supportCodimension_componentSupportEquiv Z])).trans e

/-- The inverse support map is literally the image under the component
inclusion; no new support or multiplicity is introduced. -/
@[simp]
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentDimensionSupportEquiv_symm_val (p : ℕ)
    (C : irreducibleComponents P.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (P.componentVariety C) p) :
    ((P.componentDimensionSupportEquiv p).symm ⟨C, Z⟩).1 =
      P.componentSupportImage C Z.1 := rfl

end

end OAI.AlgebraicGeometry
