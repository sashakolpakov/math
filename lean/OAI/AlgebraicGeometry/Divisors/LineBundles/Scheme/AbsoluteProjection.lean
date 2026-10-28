import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.RegularTo
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteCycleClass

/-! # Absolute Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection.BundleCycles

noncomputable section

/-! The full projection comparison after forgetting support, in both
standard degree conventions for the geometric cycle class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

theorem schemeBettiMap_cast {R : Type} [Ring R] (M : ModuleCat.{0} R)
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) {m n : ℕ} (h : m = n) (a : Betti.Scheme.schemeBetti M Y m) :
    Betti.Scheme.schemeBettiMap M n f (cast (congrArg (fun i => (Betti.Scheme.schemeBetti M Y i : Type)) h) a) =
      cast (congrArg (fun i => (Betti.Scheme.schemeBetti M X i : Type)) h) (Betti.Scheme.schemeBettiMap M m f a) := by
  subst n
  rfl

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (B : IrreducibleCloseds Y.left) (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral Z.left] [Smooth Z.hom]
    [AlgebraicGeometry.IsNoetherian Z.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z)]
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY))
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

local notation "C" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod
local notation "hc" => OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension.BundleCycles.projectionIrreducibleSupport_codimension X Y B Z πX πY hprod p hp

theorem schemeAbsoluteCycleClass_projection :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) πY (AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B p hp) =
      AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Z C p hc := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map πY)
      (Projection.RegularTo.BundleCycles.schemeProjection_support_mapsTo X Y B Z πX πY hprod) (2 * p)) (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  exact h.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Z C))ᶜ (2 * p))
    (Projection.RegularTo.BundleCycles.schemeSupportedCycleClass_projection X Y B Z πX πY hprod p hp))

theorem schemeCycleClass_projection :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πY (AbsoluteCycleClass.BundleCycles.schemeCycleClass Y B p hp) =
      AbsoluteCycleClass.BundleCycles.schemeCycleClass Z C p hc := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πY
    (cast (congrArg (fun i => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y i : Type)) (two_mul p))
      (AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B p hp)) = _
  rw [schemeBettiMap_cast (ModuleCat.of ℚ ℚ) πY (two_mul p)]
  exact congrArg (cast (congrArg (fun i => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Z i : Type)) (two_mul p)))
    (schemeAbsoluteCycleClass_projection X Y B Z πX πY hprod p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection.BundleCycles
