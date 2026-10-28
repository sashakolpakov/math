import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSupportedGysin
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.IntersectionCup

/-! # Fiber Class Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberClassPullback.BundleCycles

noncomputable section

/-! Actual supported pullback to a smooth principal fiber equals the canonical class of the existing full Cartier fiber cycle. The proof cancels the genuine supported Gysin isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionBasicOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions

theorem closedZeroFiber_analyticImage {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : X ⟶ Y) [IsClosedImmersion i.left]
    (s : Γ(Y.left, ⊤)) (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ) :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) = Set.range (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage Y s) := by
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion i).trans
  apply Eq.trans ?_ (CycleClass.Thom.GlobalSectionUnitEvaluation.Constructions.SchemeEquation.sectionZeroImage_range Y s).symm
  ext x
  have hr := congrArg (fun A : Set Y.left => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ A) hzero
  exact hr.to_iff.trans ((not_congr (CycleClass.Thom.GlobalSectionBasicOpen.Constructions.underlying_mem_basicOpen_iff Y s x)).trans not_not)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (s : Γ(Y.left, ⊤))
  (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ)
  (hi : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hlocal : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ∃ (U : Y.left.Opens), IsAffineOpen U ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen Y U ∧
    RingHom.ker (i.left.app U).hom = Ideal.span {Y.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s})
  (d p : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom (d + 1))
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hi hd in
omit [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem principalFiberParent_codimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x.val) Y.hom + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  have h := Closed.SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d 1 p hi hd
  have hx := x.property
  omega

include hzero hlocal in
theorem principalFiberSupportedClass_eq_pullback
    (hs : CartierCycle.BundleCycles.supportRegularFunction s (irreducibleSetEquivPoints.symm x.val) ≠ 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (A := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)))ᶜ)
      (B := (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)))ᶜ)
      (fun _ hx => hx) (2 * p)
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (irreducibleSetEquivPoints.symm x.val) p
        (principalFiberParent_codimension hi d p x hd)) =
    FiberSupportedGysin.BundleCycles.principalFiberSupportedClass i s d p x hd := by
  let Z := CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi
  let W := irreducibleSetEquivPoints.symm x.val
  let v := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W
  let hv := Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y W
  let hp := principalFiberParent_codimension hi d p x hd
  have hs0 : s ≠ 0 := by
    intro he
    apply hs
    change (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop s) = 0
    rw [he, map_zero, map_zero]
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Set.range Z.regularComplementInclusion)ᶜ) 2 Z.regularThomClass
  apply (ModuleCat.mono_iff_injective (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := p) Z a ha v hv).hom).mp inferInstance
  have hcu := CycleClass.Thom.Intersection.Gysin.Constructions.imageIntersectionCup_eq_gysin_pullback (q := p) Z a ha v hv
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp)
  have hc := IntersectionCup.BundleCycles.principalIntersectionCup_eq_principalClass i s hs0 (closedZeroFiber_analyticImage i s hzero)
    hi hlocal W p hp d (Closed.SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d 1 p hi hd) hs
  have hg := FiberSupportedGysin.BundleCycles.principalFiberSupportedClass_gysin i s hzero d p x hi hd a ha
  exact hcu.symm.trans (hc.trans hg.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberClassPullback.BundleCycles
