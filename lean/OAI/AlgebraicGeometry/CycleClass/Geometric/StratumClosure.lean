import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumDimension

/-! # Stratum Closure -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Reduced closures of integral locally closed strata

The scheme-theoretic image of a quasi-compact morphism from a reduced scheme
has radical ideal sheaf. For an integral source this identifies that image
with the actual reduced irreducible closure of its range. An immersion is
therefore a genuine open immersion into its reduced closure. This supplies
equality of their native dimensions and strict dimension bounds for strata
contained in singular loci.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- The kernel ideal sheaf of a quasi-compact map from a reduced scheme is
radical, because its affine section ideals are kernels into reduced rings. -/
theorem StratumClosure.kernel_radical_of_reduced [IsReduced Y] (i : Y ⟶ X) [QuasiCompact i] :
    i.ker.radical = i.ker := by
  ext U : 2
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact (Ideal.isRadical_bot.comap (i.app U).hom).radical

/-- The actual irreducible closed subset obtained by closing the image of an
integral scheme. -/
def StratumClosure.integralImageClosure [IsIntegral Y] (i : Y ⟶ X) : IrreducibleCloseds X :=
  ⟨closure (Set.range i), (by
    have hi : IsIrreducible (Set.range i) := by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ Y).image i i.continuous.continuousOn
    exact hi.closure), isClosed_closure⟩

@[simp]
theorem StratumClosure.integralImageClosure_coe [IsIntegral Y] (i : Y ⟶ X) :
    (StratumClosure.integralImageClosure i : Set X) = closure (Set.range i) := rfl

/-- The image ideal is precisely the vanishing ideal of the actual closure,
not merely an ideal with the same topological support. -/
theorem StratumClosure.kernel_eq_reducedImageClosureIdeal [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] : i.ker = GenericPoint.reducedSupportIdeal (StratumClosure.integralImageClosure i) := by
  change i.ker = Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (Set.range i), isClosed_closure⟩
  have hs : (⟨closure (Set.range i), isClosed_closure⟩ : Closeds X) = i.ker.support := by
    apply SetLike.coe_injective
    exact i.support_ker.symm
  rw [hs, Scheme.IdealSheafData.vanishingIdeal_support, StratumClosure.kernel_radical_of_reduced i]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual scheme-theoretic image is canonically the reduced induced
scheme on the irreducible closure. -/
def StratumClosure.reducedImageClosureIso [IsIntegral Y] (i : Y ⟶ X) [QuasiCompact i] :
    i.image ≅ GenericPoint.reducedSupportScheme (StratumClosure.integralImageClosure i) where
  hom := Scheme.IdealSheafData.inclusion (StratumClosure.kernel_eq_reducedImageClosureIdeal i).ge
  inv := Scheme.IdealSheafData.inclusion (StratumClosure.kernel_eq_reducedImageClosureIdeal i).le
  hom_inv_id := by
    rw [Scheme.IdealSheafData.inclusion_comp]
    exact Scheme.IdealSheafData.inclusion_id _
  inv_hom_id := by
    rw [Scheme.IdealSheafData.inclusion_comp]
    exact Scheme.IdealSheafData.inclusion_id _

@[reassoc]
theorem StratumClosure.reducedImageClosureIso_hom_inclusion [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] :
    (StratumClosure.reducedImageClosureIso i).hom ≫ GenericPoint.reducedSupportι (StratumClosure.integralImageClosure i) =
      i.imageι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- Factorization of the given map through its genuine reduced closure. -/
def StratumClosure.toReducedImageClosure [IsIntegral Y] (i : Y ⟶ X) [QuasiCompact i] :
    Y ⟶ GenericPoint.reducedSupportScheme (StratumClosure.integralImageClosure i) :=
  i.toImage ≫ (StratumClosure.reducedImageClosureIso i).hom

@[reassoc]
theorem StratumClosure.toReducedImageClosure_inclusion [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] :
    StratumClosure.toReducedImageClosure i ≫ GenericPoint.reducedSupportι (StratumClosure.integralImageClosure i) = i := by
  rw [StratumClosure.toReducedImageClosure, Category.assoc, StratumClosure.reducedImageClosureIso_hom_inclusion,
    Scheme.Hom.toImage_imageι]

/-- A quasi-compact integral immersion is open in its actual reduced closure. -/
instance StratumClosure.toReducedImageClosure_isOpenImmersion [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] [IsImmersion i] : IsOpenImmersion (StratumClosure.toReducedImageClosure i) := by
  unfold StratumClosure.toReducedImageClosure
  infer_instance

/-- This open factor has dense range in its irreducible reduced closure. -/
theorem StratumClosure.toReducedImageClosure_denseRange [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] [IsImmersion i] : DenseRange (StratumClosure.toReducedImageClosure i) :=
  IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (StratumClosure.toReducedImageClosure i).isOpenEmbedding.isOpenMap

variable {K : Type u} [Field K]

/-- The native dimension of an integral locally closed immersion equals that
of its genuine irreducible closed support. -/
theorem StratumClosure.schemeTranscendenceDimension_eq_imageClosure [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] [IsImmersion i] (f : X ⟶ Spec (.of K)) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (StratumClosure.integralImageClosure i) f := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (StratumClosure.toReducedImageClosure i) (SupportFiniteType.supportStructureMap (StratumClosure.integralImageClosure i) f)
  simpa only [SupportFiniteType.supportStructureMap, Foundations.Scheme.SupportDimension.supportTranscendenceDimension, ← Category.assoc,
    StratumClosure.toReducedImageClosure_inclusion] using h

section

variable {S : Scheme.{u}} {f : X ⟶ S}

/-- A stratum in a Noetherian ambient space is itself Noetherian. -/
instance IntegralSmoothStratification.IntegralSmoothGeometricPiece.carrier_noetherianSpace [NoetherianSpace X]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : NoetherianSpace P.carrier :=
  P.inclusion.isEmbedding.isInducing.noetherianSpace

/-- The actual irreducible closure of a stratum's image. -/
def IntegralSmoothStratification.IntegralSmoothGeometricPiece.closureSupport (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : IrreducibleCloseds X :=
  StratumClosure.integralImageClosure P.inclusion

@[simp]
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.closureSupport_coe (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    (P.closureSupport : Set X) = closure P.support := rfl

/-- The stratum as an actual open subscheme of its reduced irreducible closure. -/
def IntegralSmoothStratification.IntegralSmoothGeometricPiece.toReducedClosure [NoetherianSpace X] (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.carrier ⟶ GenericPoint.reducedSupportScheme P.closureSupport :=
  StratumClosure.toReducedImageClosure P.inclusion

instance IntegralSmoothStratification.IntegralSmoothGeometricPiece.toReducedClosure_isOpenImmersion [NoetherianSpace X]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : IsOpenImmersion P.toReducedClosure :=
  inferInstanceAs (IsOpenImmersion (StratumClosure.toReducedImageClosure P.inclusion))

@[reassoc]
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.toReducedClosure_inclusion [NoetherianSpace X]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.toReducedClosure ≫ GenericPoint.reducedSupportι P.closureSupport = P.inclusion :=
  StratumClosure.toReducedImageClosure_inclusion P.inclusion

/-- The generic-stalk comparison preserves the actual base-field scalar map. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_eq_closure [NoetherianSpace X] {f : X ⟶ Spec (.of K)}
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.dimension = Foundations.Scheme.SupportDimension.supportTranscendenceDimension P.closureSupport f :=
  StratumClosure.schemeTranscendenceDimension_eq_imageClosure P.inclusion f

/-- A stratum contained in a closed irreducible support has its entire
irreducible closure in that support. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.closureSupport_le_of_support_subset {f : X ⟶ Spec (.of K)}
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ (Z : Set X)) : P.closureSupport ≤ Z :=
  closure_minimal hP Z.isClosed

/-- The actual native dimension is bounded by any irreducible closed support
containing the stratum. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_le_of_support_subset [NoetherianSpace X]
    {f : X ⟶ Spec (.of K)} [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ (Z : Set X)) :
    P.dimension ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.dimension_eq_closure]
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f).monotone
    (P.closureSupport_le_of_support_subset Z hP)

/-- Closing a stratum inside the closed singular boundary and using strict
dimension drop gives the bound for the actual locally closed carrier. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_lt_of_support_subset_singularBoundary [NoetherianSpace X]
    [PerfectField K] {f : X ⟶ Spec (.of K)} [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ StratumDimension.supportSingularBoundary Z f) :
    P.dimension < Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.dimension_eq_closure]
  apply StratumDimension.supportTranscendenceDimension_lt_of_subset_singularBoundary P.closureSupport Z f
  exact closure_minimal hP (StratumDimension.isClosed_supportSingularBoundary Z f)

end

/-- A genuine irreducible closed subset of the singular locus has strictly
smaller native dimension than the integral ambient scheme itself. -/
theorem StratumClosure.supportTranscendenceDimension_lt_of_subset_singularLocus [IsIntegral X]
    [PerfectField K] (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (hZ : (Z : Set X) ⊆ SingularLocus.singularLocus f) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f < Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hZT : Z < T := by
    apply lt_of_le_not_ge (Set.subset_univ _)
    intro hTZ
    exact SingularLocus.genericPoint_not_mem_singularLocus f (hZ (hTZ (Set.mem_univ _)))
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt Z T f hZT).trans_le
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le T f)

/-- Every actual integral locally closed smooth stratum contained in the
singular locus has strictly smaller native dimension. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_lt_of_support_subset_singularLocus
    [IsIntegral X] [NoetherianSpace X] [PerfectField K]
    {f : X ⟶ Spec (.of K)} [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (hP : P.support ⊆ SingularLocus.singularLocus f) :
    P.dimension < Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  rw [P.dimension_eq_closure]
  apply StratumClosure.supportTranscendenceDimension_lt_of_subset_singularLocus P.closureSupport f
  exact closure_minimal hP (SingularLocus.isClosed_singularLocus f)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
