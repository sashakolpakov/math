import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalFunctions
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

/-! # Functions -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Global functions on the actual integral and special-fiber abelian models, with surjective reduction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.integral_functions_isIso : IsIso A.integral.scheme.hom.appTop :=
  Integral.GlobalFunctions.IntegralGlobalFunctions.appTop_isIso A.integral

theorem Geometry.AbelianH1Model.specialFiber_functions_isIso : IsIso A.specialFiber.scheme.hom.appTop :=
  Integral.GlobalFunctions.IntegralGlobalFunctions.appTop_isIso A.specialFiber

theorem Geometry.AbelianH1Model.specialFiber_functions_surjective :
    Function.Surjective
      (pullback.fst A.integral.scheme.hom (Geometry.scalarBaseMap (PadicInt.toZMod : ℤ_[q] →+* ZMod q))).appTop.hom :=
  Integral.GlobalFunctions.IntegralGlobalFunctions.baseChange_surjective A.integral PadicInt.toZMod
    (ZMod.ringHom_surjective PadicInt.toZMod)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
