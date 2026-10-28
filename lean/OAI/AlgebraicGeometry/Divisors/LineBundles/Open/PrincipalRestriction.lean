import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Principal Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: complete principal-divisor restriction to an open

On a nonempty restricted integral support the actual function-field map
preserves all local orders. When the open misses the support, every
coefficient vanishes. These comparisons include all ambient points.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

theorem schemePrincipalPointDivisor_off_support (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : X) (hx : x ∉ (W : Set X)) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g x = 0 := by
  have hr : x ∉ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact hx
  exact Finsupp.embDomain_of_notMem_range _ _ _ hr

variable (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds Y)

def openRestrictedRationalFunction [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (SupportRestriction.BundleCycles.openRestrictedSupport i W)).functionField :=
  RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (SupportRestriction.BundleCycles.openRestrictedSupportMap i W) g

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem openRestrictedRationalFunction_ne_zero [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    openRestrictedRationalFunction i W g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (SupportRestriction.BundleCycles.openRestrictedSupportMap i W)).hom.injective).mpr hg

/-- Restriction to a nonempty support is its genuine complete principal divisor. -/
theorem openRestriction_principalPointDivisor [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) i.isOpenEmbedding.injective.injOn =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportRestriction.BundleCycles.openRestrictedSupport i W) (openRestrictedRationalFunction i W g) := by
  ext x
  by_cases hx : x ∈ (SupportRestriction.BundleCycles.openRestrictedSupport i W : Set X)
  · have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W)) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact hx
    obtain ⟨y, rfl⟩ := hr
    have hp : CycleClass.Geometric.GenericPoint.reducedSupportι W (SupportRestriction.BundleCycles.openRestrictedSupportMap i W y) =
        i (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y) :=
      congrArg (fun j => j y) (SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion i W)
    change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (i (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y)) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (SupportRestriction.BundleCycles.openRestrictedSupport i W)
        (openRestrictedRationalFunction i W g) (CycleClass.Geometric.GenericPoint.reducedSupportι (SupportRestriction.BundleCycles.openRestrictedSupport i W) y)
    rw [← hp, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support]
    exact congrArg (fun n : ℤ => (n : ℚ))
      (RationalDivisorRestriction.BundleCycles.ord_openImmersion (SupportRestriction.BundleCycles.openRestrictedSupportMap i W) g y).symm
  · have hi : i x ∉ (W : Set Y) := fun h => hx
      ((congrArg (fun s : Set X => x ∈ s) (SupportRestriction.BundleCycles.openRestrictedSupport_coe i W)).mpr h)
    exact (schemePrincipalPointDivisor_off_support W g (i x) hi).trans
      (schemePrincipalPointDivisor_off_support (SupportRestriction.BundleCycles.openRestrictedSupport i W)
        (openRestrictedRationalFunction i W g) x hx).symm

omit [AlgebraicGeometry.IsNoetherian X] in
/-- If the open misses the support, its entire principal divisor restricts to zero. -/
theorem openRestriction_principalPointDivisor_empty [IsEmpty (SupportRestriction.BundleCycles.openSupportPullback i W)]
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g) i.isOpenEmbedding.injective.injOn = 0 := by
  ext x
  apply schemePrincipalPointDivisor_off_support W g (i x)
  intro hx
  have hn := (SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff i W).mpr ⟨x, hx⟩
  exact isEmptyElim (Classical.choice hn)

end

/-!
# LineBundleCycles: lifting open supports and rational functions to their closures

A reduced integral closed support in an open subscheme is open in its
actual reduced closure in the ambient scheme. Its function field is
therefore canonically unchanged. This supplies concrete ambient
principal divisors lifting the relations on the open.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds X)

def openClosureSupport : IrreducibleCloseds Y := CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

omit [AlgebraicGeometry.IsNoetherian X] [IsOpenImmersion i] in
theorem openClosureSupport_coe : (openClosureSupport i W : Set Y) = closure (i '' (W : Set X)) := by
  change closure (Set.range (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W)) = _
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

omit [AlgebraicGeometry.IsNoetherian X] in
theorem openClosureSupport_preimage : i ⁻¹' (openClosureSupport i W : Set Y) = (W : Set X) := by
  rw [openClosureSupport_coe,
    i.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage i.continuous,
    Set.preimage_image_eq _ i.isOpenEmbedding.injective, W.isClosed.closure_eq]

/-- The original support as the actual open subscheme of its reduced closure. -/
def openSupportClosureMap : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (openClosureSupport i W) :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

instance openSupportClosureMap_isOpenImmersion : IsOpenImmersion (openSupportClosureMap i W) :=
  inferInstanceAs (IsOpenImmersion (CycleClass.Geometric.StratumClosure.toReducedImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)))

omit [IsOpenImmersion i] in
theorem openSupportClosureMap_inclusion :
    openSupportClosureMap i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (openClosureSupport i W) = CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

theorem openClosureSupport_dimension (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (openClosureSupport i W) f = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) f
  exact h.symm.trans (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) (Category.assoc _ _ _))

/-- Extend the rational function through the actual generic-stalk isomorphism. -/
def openClosureRationalFunction (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (openClosureSupport i W)).functionField :=
  (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (openSupportClosureMap i W)).inv g

theorem openClosureRationalFunction_ne_zero (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    openClosureRationalFunction i W g ≠ 0 :=
  (map_ne_zero_iff _ (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (openSupportClosureMap i W)).inv.hom.injective).mpr hg

variable [AlgebraicGeometry.IsNoetherian Y]

/-- The complete ambient principal divisor restricts to the original one. -/
theorem openClosure_principalPointDivisor (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Finsupp.comapDomain i
        (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (openClosureSupport i W) (openClosureRationalFunction i W g))
        i.isOpenEmbedding.injective.injOn = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  ext x
  by_cases hx : x ∈ (W : Set X)
  · have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact hx
    obtain ⟨y, rfl⟩ := hr
    have hp : CycleClass.Geometric.GenericPoint.reducedSupportι (openClosureSupport i W) (openSupportClosureMap i W y) =
        i (CycleClass.Geometric.GenericPoint.reducedSupportι W y) := congrArg (fun j => j y) (openSupportClosureMap_inclusion i W)
    change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (openClosureSupport i W) (openClosureRationalFunction i W g)
      (i (CycleClass.Geometric.GenericPoint.reducedSupportι W y)) = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g (CycleClass.Geometric.GenericPoint.reducedSupportι W y)
    rw [← hp, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support]
    have he : RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (openSupportClosureMap i W) (openClosureRationalFunction i W g) = g :=
      Iso.inv_hom_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso (openSupportClosureMap i W)) g
    exact congrArg (fun n : ℤ => (n : ℚ))
      ((RationalDivisorRestriction.BundleCycles.ord_openImmersion (openSupportClosureMap i W) (openClosureRationalFunction i W g) y).symm.trans
        (congrArg (fun a => (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord a y) he))
  · have hi : i x ∉ (openClosureSupport i W : Set Y) :=
      fun h => hx ((congrArg (fun s : Set X => x ∈ s) (openClosureSupport_preimage i W)).mp h)
    exact (schemePrincipalPointDivisor_off_support (openClosureSupport i W)
      (openClosureRationalFunction i W g) (i x) hi).trans (schemePrincipalPointDivisor_off_support W g x hx).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction.BundleCycles
