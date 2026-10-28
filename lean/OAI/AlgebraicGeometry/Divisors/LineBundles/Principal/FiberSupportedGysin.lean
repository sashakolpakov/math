import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleGysin

/-! # Fiber Supported Gysin -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSupportedGysin.BundleCycles

noncomputable section

/-! The actual principal Cartier fiber cycle maps under supported Gysin to the canonical class of the full original principal divisor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (s : Γ(Y.left, ⊤))
  (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ)
  (d p : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom (d + 1))
  (hi : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

def principalFiberSupportedClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)))ᶜ (2 * p) :=
  Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d p hd
    (FiberSupportedCycle.BundleCycles.principalFiberSupportedCycle i s d x)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).regularComplementInclusion)ᶜ) 2)
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi).regularThomClass)

include hzero in
theorem principalFiberSupportedClass_gysin :
    (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := p) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i 1 hi) a ha
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))
      (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y (irreducibleSetEquivPoints.symm x.val))).hom
      (principalFiberSupportedClass i s d p x hd) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y
      (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)))
      d (1 + p) (Closed.SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d 1 p hi hd)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle Y
        (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d
        (CartierFiber.BundleCycles.principalCartierGradedCycle s Y.hom d x)) := by
  have h := Closed.SupportedCycleGysin.BundleCycles.closedSupportedCycle_gysin_eq_fullPush i
    (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))
    (Scheme.SupportSectionCup.BundleCycles.schemeSupport_openComplement Y (irreducibleSetEquivPoints.symm x.val)) d 1 p hi hd a ha
    (FiberSupportedCycle.BundleCycles.principalFiberSupportedCycle i s d x)
  exact h.trans (congrArg (fun c => Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y
    (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)))
    d (1 + p) (Closed.SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d 1 p hi hd)
    (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle Y
      (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val))) d c))
    (FiberSupportedCycle.BundleCycles.principalFiberSupportedCycle_push i s d x hzero))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberSupportedGysin.BundleCycles
