import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSectionCup
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeNormalization.SectionGerm
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # Support Section -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSection.BundleCycles

noncomputable section

/-! The full principal divisor of a section on an arbitrary integral support lies in its actual intersection with the section zero set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (W : IrreducibleCloseds X.left) (s : Γ(X.left, ⊤))

local instance supportSectionGeometryTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩

def schemeSupportSectionClosed : Closeds X.left :=
  ⟨(W : Set X.left) ∩ (X.left.basicOpen s : Set X.left)ᶜ,
    W.isClosed.inter (X.left.basicOpen s).isOpen.isClosed_compl⟩

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportSectionClosed_analytic :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' (schemeSupportSectionClosed X W s : Set X.left) =
      SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s := by
  ext x
  rw [SupportSectionCup.BundleCycles.schemeSupportSectionIntersection, Set.mem_inter_iff, CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range, CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range]
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ (W : Set X.left) ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∉ X.left.basicOpen s) ↔ _
  rw [CycleClass.Thom.GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff]
  simp only [not_not, Set.mem_preimage, Set.mem_ofPred_eq]

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemePrincipalSectionPoint_mem (x : X.left)
    (hx : Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) x ≠ 0) :
    x ∈ schemeSupportSectionClosed X W s := by
  have hw : x ∈ (W : Set X.left) := by
    by_contra h
    exact hx (Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support W _ x h)
  have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]; exact hw
  obtain ⟨z, rfl⟩ := hr
  refine ⟨hw, ?_⟩
  intro hz
  have hpre := Scheme.preimage_basicOpen_top (CycleClass.Geometric.GenericPoint.reducedSupportι W) s
  have hzb : z ∈ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).basicOpen ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) :=
    (congrArg (fun U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens => z ∈ U) hpre).mp hz
  have h0 := RegularDivisor.BundleCycles.regularFunctionDivisor_eq_zero_of_isUnit_germ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
    ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) z
    (((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).mem_basicOpen _ z (Opens.mem_top _)).mp hzb)
  exact hx ((Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support W _ z).trans
    ((congrArg (fun n : ℤ => (n : ℚ)) h0).trans Int.cast_zero))

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeGradedPrincipalSection_supported (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d)
    (hz : Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor X.hom d W
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)) z ≠ 0) :
    Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X (irreducibleSetEquivPoints.symm z.val)) ⊆ SupportSectionCup.BundleCycles.schemeSupportSectionIntersection X W s := by
  have hp : (irreducibleSetEquivPoints.symm z.val : Set X.left) ⊆ schemeSupportSectionClosed X W s :=
    closure_minimal (Set.singleton_subset_iff.mpr (schemePrincipalSectionPoint_mem X W s z.val hz))
      (schemeSupportSectionClosed X W s).isClosed
  intro y hy
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range] at hy
  exact (Set.ext_iff.mp (schemeSupportSectionClosed_analytic X W s) y).mp (hp hy)

variable (hs : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0)

include hs in
omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportSection_generic_mem_basicOpen :
    irreducibleSetEquivPoints W ∈ X.left.basicOpen s := by
  rw [← CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W]
  change genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ∈ (CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ X.left.basicOpen s
  rw [Scheme.preimage_basicOpen_top, (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).mem_basicOpen _ _ (Opens.mem_top _)]
  exact isUnit_iff_ne_zero.mpr hs

include hs in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeSupportSectionClosed_codimension (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (A : IrreducibleCloseds X.left) (hA : (A : Set X.left) ⊆ schemeSupportSectionClosed X W s) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom + (p + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  have hle : A ≤ W := fun _ hx => (hA hx).1
  have hne : A ≠ W := by
    intro he
    subst A
    exact (hA (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem).2
      (schemeSupportSection_generic_mem_basicOpen X W s hs)
  have hlt := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt A W X.hom (lt_of_le_of_ne hle hne)
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportSection.BundleCycles
