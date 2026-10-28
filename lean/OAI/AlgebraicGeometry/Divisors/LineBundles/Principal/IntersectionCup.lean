import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GlobalSectionFormula
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalImmersionPair
import OAI.AlgebraicGeometry.Divisors.LineBundles.ImageIntersectionRightSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.ImageIntersectionCupSwap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedClassTransport

/-! # Intersection Cup -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.IntersectionCup.BundleCycles

noncomputable section

/-! The actual fiber Thom class intersected with any parent cycle gives the canonical class of the full principal divisor, in the original common support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Transport.Constructions.Class

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (s : Γ(Y.left, ⊤)) (hs : s ≠ 0)
  (hzero : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) = Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s))
  (hi : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hlocal : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ∃ (U : Y.left.Opens), IsAffineOpen U ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen Y U ∧
    RingHom.ker (i.left.app U).hom = Ideal.span {Y.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s})
  (W : IrreducibleCloseds Y.left) (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

include hs hlocal in
theorem schemeSupportSectionCup_changeToFiber :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (ImageIntersectionRightSupport.BundleCycles.imageIntersectionRightSupport_mapsTo (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) hzero) (2 * (p + 1)) (Scheme.SupportSectionCup.BundleCycles.schemeSupportSectionCup Y W s p hp) =
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i)
      (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y W) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).closed.isClosed_range.isOpen_compl p 1
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).regularThomClass := by
  have h := ImageIntersectionRightSupport.BundleCycles.imageIntersectionCup_rightSupport (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) hzero (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y W) (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_openComplement Y s)
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).closed.isClosed_range.isOpen_compl p 1
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp) (Finite.GlobalSectionClassRestriction.BundleCycles.schemeSectionSupportedClass Y s)
  exact h.trans (congrArg (CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i)
    (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y W) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).closed.isClosed_range.isOpen_compl p 1
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp))
    (Scheme.PrincipalImmersionPair.BundleCycles.schemePrincipalImmersion_sectionClass_eq_Thom i s hzero hs hi hlocal))

local instance principalIntersectionCupSupportTop : Nonempty (⊤ : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens) :=
  ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Opens.mem_top _⟩⟩

include hs hzero hlocal in
theorem principalIntersectionCup_eq_principalClass (d : ℕ)
    (hd : d + (1 + p) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (hW : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) ≠ 0) :
    CycleClass.Thom.ImageIntersectionCup.Constructions.imageIntersectionCup (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W)
      (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).closed.isClosed_range.isOpen_compl (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y W) 1 p
      (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).regularThomClass (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W))
      d (1 + p) hd
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W)) d
        (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor Y.hom d W
          ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s)))) := by
  let u := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W
  let v := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i
  let F := Set.range u ∩ Set.range v
  let G := Set.range v ∩ Set.range u
  let hd' : d + (p + 1) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by omega
  let c := Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor Y.hom d W
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s))
  have hF : Scheme.SupportSectionCup.BundleCycles.schemeSupportSectionIntersection Y W s = F := congrArg (Set.inter (Set.range u)) hzero.symm
  have hclass := Closed.SupportedClassTransport.BundleCycles.schemeClosedRestrictedClass_identityMap Y (Scheme.SupportSectionCup.BundleCycles.schemeSupportSectionIntersection Y W s) F hF
    (ImageIntersectionRightSupport.BundleCycles.imageIntersectionRightSupport_mapsTo u (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) v hzero) d (p + 1) hd' c
  have hformula := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
    (ImageIntersectionRightSupport.BundleCycles.imageIntersectionRightSupport_mapsTo u (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) v hzero) (2 * (p + 1)))
    (Scheme.GlobalSectionFormula.BundleCycles.schemeSupportSectionCup_eq_principalSupportedClass Y W s p hp d hd' hW)
  have hcup := (schemeSupportSectionCup_changeToFiber i s hs hzero hi hlocal W p hp).symm.trans
    (hformula.trans hclass)
  have hswap := ImageIntersectionCupSwap.BundleCycles.imageIntersectionCup_swap u v (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y W)
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).closed.isClosed_range.isOpen_compl p 1
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).regularThomClass
  have htransport := congrArg (CycleClass.Thom.Supported.Transport.Constructions.Class.supportDegreeTransport (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (congrArg Set.compl (Set.inter_comm (Set.range u) (Set.range v)))
    (congrArg (fun n => 2 * n) (Nat.add_comm p 1))) hcup
  exact hswap.symm.trans (htransport.trans (Closed.SupportedClassTransport.BundleCycles.schemeClosedRestrictedClass_supportDegreeTransport Y F G
    (Set.inter_comm _ _) d (p + 1) (1 + p) (Nat.add_comm p 1) hd' hd c))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.IntersectionCup.BundleCycles
