import OAI.ArithmeticGeometry.Descent.CMVariety.EnhancedChart
import OAI.ArithmeticGeometry.Descent.CMVariety.ComplexParameter
import OAI.ArithmeticGeometry.Descent.CMVariety.PresentedTupleComparison

/-! # Enhanced Parameter Complex -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! The actual complex base change of the constructed arithmetic parameter,
with full enhanced comparisons, geometric presentations, and exact tuple recovery. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def StandardModuli.Abelian.ComplexAbelianPresentation.transportEnhanced
    {g N r : ℕ} {δ : Fin g → ℕ} {A B : ModuliObjects.Abelian.EnhancedAbelianData g δ N r AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (e : ModuliObjects.Abelian.EnhancedAbelianIso A B) (P : StandardModuli.Abelian.ComplexAbelianPresentation B.polarized.abelian) :
    StandardModuli.Abelian.ComplexAbelianPresentation A.polarized.abelian := by
  let : IsMonHom e.polarized.abelian.hom := e.polarized.abelianGroup
  exact P.transport e.polarized.abelian

variable {X : Scheme} {f : X ⟶ Spec (CommRingCat.of ℚ)}
  {g N r m : ℕ} {δ : Fin g → ℕ}
  {A : ModuliObjects.Abelian.EnhancedAbelianData g δ N r X} {p : Spec (CommRingCat.of ℂ) ⟶ X}
  {k : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) (A.pullback p).polarized.abelian}
  (D : EnhancedChart.Abelian.SmoothEnhancedParameter f A p k)

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeBase : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := ComplexParameter.Abelian.arithmeticComplexBase (D.map ≫ f)

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeProjection : D.nativeBase.left ⟶ D.space :=
  pullback.fst (D.map ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

instance EnhancedChart.Abelian.SmoothEnhancedParameter.nativeBase_smooth : Smooth D.nativeBase.hom := by
  change Smooth (pullback.snd (D.map ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
  infer_instance

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeCenter : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase := ComplexParameter.Abelian.arithmeticComplexPoint (D.map ≫ f) D.point

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeCenter_projection : D.nativeCenter.left ≫ D.nativeProjection = D.point :=
  ComplexParameter.Abelian.arithmeticComplexPoint_projection (D.map ≫ f) D.point

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativePointMap (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase) : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X :=
  (s.left ≫ D.nativeProjection) ≫ D.map

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.nativeCenter_original : D.nativePointMap D.nativeCenter = p := by
  dsimp only [EnhancedChart.Abelian.SmoothEnhancedParameter.nativePointMap]
  rw [D.nativeCenter_projection, D.point_eq]

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeFamily : ModuliObjects.Abelian.EnhancedAbelianData g δ N r D.nativeBase.left := D.family.pullback D.nativeProjection

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeExtraTuple : AbelianEndomorphism.AbelianEndomorphismTuple (Fin m) D.nativeFamily.polarized.abelian :=
  D.extraTuple.pullback D.nativeProjection

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeFiberIso (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase) :
    ModuliObjects.Abelian.EnhancedAbelianIso (D.nativeFamily.pullback s.left) (A.pullback (D.nativePointMap s)) :=
  (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackComp D.family D.nativeProjection s.left).trans
    ((D.comparison.pullback (s.left ≫ D.nativeProjection)).trans
      (ModuliObjects.Abelian.EnhancedAbelianIso.pullbackComp A D.map (s.left ≫ D.nativeProjection)))

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativePresentation
    (present : ∀ x : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X, StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback x).polarized.abelian)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase) :
    StandardModuli.Abelian.ComplexAbelianPresentation (D.nativeFamily.polarized.abelian.pullback s.left) :=
  (present (D.nativePointMap s)).transportEnhanced (D.nativeFiberIso s)

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeCenterIso : ModuliObjects.Abelian.EnhancedAbelianIso (D.nativeFamily.pullback D.nativeCenter.left) (A.pullback p) :=
  EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison D.family D.nativeProjection D.nativeCenter.left D.point
    D.nativeCenter_projection (A.pullback p) D.fiberComparison

def EnhancedChart.Abelian.SmoothEnhancedParameter.nativeCenterPresentation (P : StandardModuli.Abelian.ComplexAbelianPresentation (A.pullback p).polarized.abelian) :
    StandardModuli.Abelian.ComplexAbelianPresentation (D.nativeFamily.polarized.abelian.pullback D.nativeCenter.left) :=
  P.transportEnhanced D.nativeCenterIso

theorem EnhancedChart.Abelian.SmoothEnhancedParameter.native_extraRecovery :
    AbelianEndomorphism.ConjugateAbelianTuples D.nativeCenterIso.polarized.abelian
      (D.nativeExtraTuple.pullback D.nativeCenter.left) k := by
  change AbelianEndomorphism.ConjugateAbelianTuples
    (EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison D.family D.nativeProjection D.nativeCenter.left D.point
      D.nativeCenter_projection (A.pullback p) D.fiberComparison).polarized.abelian
    ((D.extraTuple.pullback D.nativeProjection).pullback D.nativeCenter.left) k
  rw [EnhancedCoefficientComparisons.Abelian.restrictedEnhancedFiberComparison_abelian]
  exact RestrictedTupleComparison.Abelian.restricted_tuple_comparison D.family.polarized.abelian D.nativeProjection D.nativeCenter.left D.point
    D.nativeCenter_projection (A.pullback p).polarized.abelian D.fiberComparison.polarized.abelian
    D.extraTuple k D.extraRecovery

end

end OAI.ArithmeticGeometry.Descent.CMVariety
