import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothAbelianFiber
import OAI.ArithmeticGeometry.Descent.CMVariety.ComplexParameter

/-! # Abelian Parameter Complex -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! The native complex base of the constructed abelian parameter retains
its central presentation and every prescribed CM endomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {g : ℕ} {Index : Type} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  {k : AbelianEndomorphism.AbelianEndomorphismTuple Index A} (D : SmoothAbelianFiber.SmoothAbelianParameter A k)

def SmoothAbelianFiber.SmoothAbelianParameter.nativeBase : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := ComplexParameter.Abelian.arithmeticComplexBase D.rationalStructure

def SmoothAbelianFiber.SmoothAbelianParameter.nativeProjection : D.nativeBase.left ⟶ D.space :=
  pullback.fst D.rationalStructure (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

instance SmoothAbelianFiber.SmoothAbelianParameter.nativeBase_smooth : Smooth D.nativeBase.hom := by
  change Smooth (pullback.snd D.rationalStructure (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
  infer_instance

def SmoothAbelianFiber.SmoothAbelianParameter.nativeCenter : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase := ComplexParameter.Abelian.arithmeticComplexPoint D.rationalStructure D.point

theorem SmoothAbelianFiber.SmoothAbelianParameter.nativeCenter_projection : D.nativeCenter.left ≫ D.nativeProjection = D.point :=
  ComplexParameter.Abelian.arithmeticComplexPoint_projection D.rationalStructure D.point

def SmoothAbelianFiber.SmoothAbelianParameter.nativeFamily : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g D.nativeBase.left := D.family.pullback D.nativeProjection

def SmoothAbelianFiber.SmoothAbelianParameter.nativeExtraTuple : AbelianEndomorphism.AbelianEndomorphismTuple Index D.nativeFamily :=
  D.extraTuple.pullback D.nativeProjection

def SmoothAbelianFiber.SmoothAbelianParameter.nativePresentation (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.nativeBase) :
    StandardModuli.Abelian.ComplexAbelianPresentation (D.nativeFamily.pullback s.left) :=
  SmoothAbelianFiber.pullbackComplexFiberPresentations D.family D.nativeProjection D.present s.left

def SmoothAbelianFiber.SmoothAbelianParameter.nativeCenterIso : (D.nativeFamily.pullback D.nativeCenter.left).scheme ≅ A.scheme :=
  RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison D.family D.nativeProjection D.nativeCenter.left D.point
    D.nativeCenter_projection A D.fiberComparison

instance SmoothAbelianFiber.SmoothAbelianParameter.nativeCenterIso_group : IsMonHom D.nativeCenterIso.hom :=
  @RestrictedTupleComparison.Abelian.restrictedAbelianFiberComparison_group D.space D.nativeBase.left AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase g
    D.family D.nativeProjection D.nativeCenter.left D.point D.nativeCenter_projection A
    D.fiberComparison D.fiberComparison_group

def SmoothAbelianFiber.SmoothAbelianParameter.nativeCenterPresentation (P : StandardModuli.Abelian.ComplexAbelianPresentation A) :
    StandardModuli.Abelian.ComplexAbelianPresentation (D.nativeFamily.pullback D.nativeCenter.left) :=
  @StandardModuli.Abelian.ComplexAbelianPresentation.transport g (D.nativeFamily.pullback D.nativeCenter.left) A
    D.nativeCenterIso D.nativeCenterIso_group P

theorem SmoothAbelianFiber.SmoothAbelianParameter.native_extraRecovery :
    AbelianEndomorphism.ConjugateAbelianTuples D.nativeCenterIso (D.nativeExtraTuple.pullback D.nativeCenter.left) k :=
  RestrictedTupleComparison.Abelian.restricted_tuple_comparison D.family D.nativeProjection D.nativeCenter.left D.point
    D.nativeCenter_projection A D.fiberComparison D.extraTuple k D.extraRecovery

end

end OAI.ArithmeticGeometry.Descent.CMVariety
