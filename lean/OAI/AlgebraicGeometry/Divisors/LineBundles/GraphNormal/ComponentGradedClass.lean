import OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedCycleClass

/-! # Component Graded Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentGradedClass.BundleCycles

noncomputable section

/-! The actual graph-normal extension over each source component
commutes with the geometric class of every finite graded cycle. The
shift is the dimension of the actual receiving target component. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    (C : irreducibleComponents X.carrier)

def graphNormalComponentFiberRank : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety (Projective.MorphismComponents.BundleCycles.projectiveMorphismComponent f C)).structureMap

local notation "V" => X.componentVariety C
local notation "N" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentOver f C
local notation "q" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentCycleClass.BundleCycles.graphNormalComponentProjectionOver f C
local notation "r" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentGradedClass.BundleCycles.graphNormalComponentFiberRank f C
local notation "h" => OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentRank.BundleCycles.graphNormalComponent_hasAffineSpaceChartsOfRank f C

local instance : IsIntegral (V).toOver.left := inferInstanceAs (IsIntegral (V).carrier)
local instance : Smooth (V).toOver.hom := inferInstanceAs (Smooth (V).structureMap)
local instance : AlgebraicGeometry.IsNoetherian (V).toOver.left :=
  inferInstanceAs (AlgebraicGeometry.IsNoetherian (V).carrier)
local instance : IsLocallyNoetherian (V).toOver.left := inferInstanceAs (IsLocallyNoetherian (V).carrier)

def graphNormalComponentGradedExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (V).structureMap d →₀ ℚ) →ₗ[ℚ]
      (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (N).hom (d + r) →₀ ℚ) := AffineBundle.OverGrading.Cycles.affineBundleOverGradedExtension q r h d

theorem graphNormalComponentGradedExtension_forget (d : ℕ)
    (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (V).structureMap d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (N).hom (d + r) (graphNormalComponentGradedExtension f C d a) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (q).left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (V).structureMap d a) :=
  AffineBundle.OverGrading.Cycles.affineBundleOverGradedExtension_forget q r h d a

theorem graphNormalComponentGradedClass (d p : ℕ)
    (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (V).structureMap) :
    (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass N (d + r) p (AffineBundle.OverGrading.Cycles.affineBundleOver_complementDegree q r h d p hd)).comp
        (graphNormalComponentGradedExtension f C d) =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) q).hom.comp
        (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass (V).toOver d p hd) := AffineBundle.GradedCycleClass.Cycles.schemeGradedCycleClass_affineBundle q r h d p hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GraphNormal.ComponentGradedClass.BundleCycles
