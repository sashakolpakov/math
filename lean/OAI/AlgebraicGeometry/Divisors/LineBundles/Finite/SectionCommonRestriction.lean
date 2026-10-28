import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RegularPrincipalSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ParentGraphProjection

/-! # Section Common Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionCommonRestriction.BundleCycles

noncomputable section

section

/-! The actual finite-image section intersection has the expected support codimension, and the omitted principal boundary lies inside it with codimension one higher. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Purity.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤))

local instance finiteSectionSupportPurityTopNonempty : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

def finiteRegularSectionClosed : Closeds N.left :=
  ⟨(CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S) : Set N.left) ∩ (N.left.basicOpen s : Set N.left)ᶜ,
    (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)).isClosed.inter (N.left.basicOpen s).isOpen.isClosed_compl⟩

omit [Smooth S.hom] [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] [IsFinite k.left] in
theorem finiteRegularSectionClosed_analytic :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (finiteRegularSectionClosed k s : Set N.left) =
      RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s := by
  ext x
  rw [RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport, Set.mem_inter_iff, CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S) : Set N.left) ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∉ N.left.basicOpen s) ↔ _
  rw [CycleClass.Thom.GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff]
  simp only [not_not, Set.mem_preimage, Set.mem_ofPred_eq]

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] in
theorem finitePrincipalBoundary_subset_section :
    (PrincipalBoundary.BundleCycles.finitePrincipalBoundary (S.left.germToFunctionField ⊤ (k.left.appTop s)) k : Set N.left) ⊆
      finiteRegularSectionClosed k s := by
  intro x hx
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
  exact RegularPrincipalSupport.BundleCycles.finiteRegularPrincipal_image_support k s z
    (CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary_subset N
      (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (PrincipalBoundary.BundleCycles.finitePrincipalPrime S (S.left.germToFunctionField ⊤ (k.left.appTop s)) z)))
      (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k (CycleClass.Thom.SchemeDivisor.Purity.Constructions.primeSupport S (PrincipalBoundary.BundleCycles.finitePrincipalPrime S (S.left.germToFunctionField ⊤ (k.left.appTop s)) z))) hz)

variable (hs : S.left.germToFunctionField ⊤ (k.left.appTop s) ≠ 0)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

omit [Smooth S.hom] [AlgebraicGeometry.IsNoetherian S.left] [AlgebraicGeometry.IsIntegral N.left] [Smooth N.hom] in
include hs in
theorem finiteWholeImage_generic_mem_basicOpen :
    irreducibleSetEquivPoints (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) ∈ N.left.basicOpen s := by
  rw [CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport_genericPoint, WholeSupport.BundleCycles.wholeSchemeSupport, OrderIso.apply_symm_apply]
  change k.left (genericPoint S.left) ∈ N.left.basicOpen s
  have hpre := Scheme.preimage_basicOpen_top k.left s
  change genericPoint S.left ∈ k.left ⁻¹ᵁ N.left.basicOpen s
  rw [hpre, S.left.mem_basicOpen (k.left.appTop s) (genericPoint S.left) (Opens.mem_top _)]
  exact isUnit_iff_ne_zero.mpr hs

omit [AlgebraicGeometry.IsNoetherian S.left] in
include hs hp in
theorem finiteRegularSectionClosed_codimension (A : IrreducibleCloseds N.left)
    (hA : (A : Set N.left) ⊆ finiteRegularSectionClosed k s) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A N.hom + (p + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension N.hom := by
  have hle : A ≤ CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S) := fun x hx => (hA hx).1
  have hne : A ≠ CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S) := by
    intro he
    subst A
    have hη := (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)).isIrreducible.isGenericPoint_genericPoint
      (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)).isClosed
    exact (hA hη.mem).2 (finiteWholeImage_generic_mem_basicOpen k s hs)
  have hlt := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt A (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (WholeSupport.BundleCycles.wholeSchemeSupport S)) N.hom
    (lt_of_le_of_ne hle hne)
  have hd := WholeSupport.BundleCycles.finiteWholeImage_dimension k
  have hN := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension N.hom
  omega

end

/-! Removing the actual finite principal boundary preserves the original section-intersection supported group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [AlgebraicGeometry.IsNoetherian S.left] [IsIntegral N.left] [Smooth N.hom]
  [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)]
  (k : S ⟶ N) [IsFinite k.left] (s : Γ(N.left, ⊤))
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom)

local instance finiteSectionCommonRestrictionTop : Nonempty (⊤ : S.left.Opens) :=
  ⟨⟨genericPoint S.left, Opens.mem_top _⟩⟩

omit [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] [AlgebraicGeometry.IsNoetherian N.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)] in
theorem finiteSectionSupport_complement_le_commonOpen :
    (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ ⊆
      PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k := by
  intro x hx hy
  apply hx
  exact (Set.ext_iff.mp (finiteRegularSectionClosed_analytic k s) x).mp
    (finitePrincipalBoundary_subset_section k s hy)

include hp in
theorem finiteSectionCommonRestriction_isIso :
    IsIso (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
      (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ
      (PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen (S.left.germToFunctionField ⊤ (k.left.appTop s)) k) (2 * (p + 1))) := by
  let r := S.left.germToFunctionField ⊤ (k.left.appTop s)
  have h0 := CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedSupport_cohomology_isZero N (PrincipalBoundary.BundleCycles.finitePrincipalBoundary r k) (p + 2)
    (PrincipalBoundary.BundleCycles.finitePrincipalBoundary_codimension r k p hp) (2 * (p + 1)) (by omega)
  have h1 := CycleClass.Thom.Scheme.ClosedSupportPurity.Constructions.closedSupport_cohomology_isZero N (PrincipalBoundary.BundleCycles.finitePrincipalBoundary r k) (p + 2)
    (PrincipalBoundary.BundleCycles.finitePrincipalBoundary_codimension r k p hp) (2 * (p + 1) + 1) (by omega)
  exact CycleClass.Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction_isIso (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
    (PrincipalBoundary.BundleCycles.finitePrincipalCommonOpen r k : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) (RegularPrincipalSupport.BundleCycles.finiteRegularSectionSupport k s)ᶜ
    (finiteSectionSupport_complement_le_commonOpen k s) (2 * (p + 1)) h0 h1

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.SectionCommonRestriction.BundleCycles
