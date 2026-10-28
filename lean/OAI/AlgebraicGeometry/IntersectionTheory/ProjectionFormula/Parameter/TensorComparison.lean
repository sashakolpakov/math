import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient
import Mathlib.CategoryTheory.Whiskering

/-! # Tensor Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorComparison

noncomputable section

/-! The tensor product of parameter quotients over the quotient ring
is naturally the parameter quotient of the original tensor product. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Functor (isoWhiskerLeft isoWhiskerRight)

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] (r : R)

def baseChangeIso : ScalarQuotient.quotient R r ≅ Flat.Extension.baseChange R (ScalarQuotient.Ring R r) :=
  NatIso.ofComponents (fun M => (ScalarQuotient.baseChangeEquiv R r M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (QuotSMulTop.equivQuotTensor_naturality r f.hom) x)

def restrictedBaseChangeIso :
    Flat.Extension.baseChange R (ScalarQuotient.Ring R r) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})) ≅
        QuotientComplex.quotient R r :=
  isoWhiskerRight (baseChangeIso R r).symm _ ≪≫ ScalarQuotient.restrictionIso R r

def tensorIso (M : ModuleCat.{u} R) :
    ScalarQuotient.quotient R r ⋙ tensorLeft ((ScalarQuotient.quotient R r).obj M) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})) ≅
    tensorLeft M ⋙ QuotientComplex.quotient R r :=
  isoWhiskerRight (baseChangeIso R r) _ ≪≫
    isoWhiskerLeft (Flat.Extension.baseChange R (ScalarQuotient.Ring R r))
      (isoWhiskerRight ((tensoringLeft (ModuleCat (ScalarQuotient.Ring R r))).mapIso
        ((baseChangeIso R r).app M)) _) ≪≫
    (Functor.associator (Flat.Extension.baseChange R (ScalarQuotient.Ring R r))
      (tensorLeft ((Flat.Extension.baseChange R (ScalarQuotient.Ring R r)).obj M))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})))).symm ≪≫
    isoWhiskerRight (Flat.Extension.tensorIso R (ScalarQuotient.Ring R r) M) _ ≪≫
    Functor.associator (tensorLeft M) (Flat.Extension.baseChange R (ScalarQuotient.Ring R r))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))) ≪≫
    isoWhiskerLeft (tensorLeft M) (restrictedBaseChangeIso R r)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorComparison
