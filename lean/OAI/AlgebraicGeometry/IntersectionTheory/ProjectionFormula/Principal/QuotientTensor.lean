import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorSpecialization

/-! # Quotient Tensor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientTensor

noncomputable section

/-! Quotienting the first tensor factor by a scalar gives the
scalar quotient of the tensor complex, over the original ring. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Functor (isoWhiskerLeft)

universe u

variable (R : Type u) [CommRing R] (r : R)

def quotientIso : Parameter.QuotientComplex.quotient R r ≅
    tensorLeft (ModuleCat.of R (R ⧸ Ideal.span {r})) :=
  NatIso.ofComponents (fun M => (QuotSMulTop.equivQuotTensor r M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    exact QuotSMulTop.equivQuotTensor_naturality r f.hom)

def tensorIso (M : ModuleCat.{u} R) :
    tensorLeft ((Parameter.QuotientComplex.quotient R r).obj M) ≅
      tensorLeft M ⋙ Parameter.QuotientComplex.quotient R r :=
  (tensoringLeft (ModuleCat R)).mapIso ((quotientIso R r).app M) ≪≫
    tensorLeftTensor (.of R (R ⧸ Ideal.span {r})) M ≪≫
      isoWhiskerLeft (tensorLeft M) (quotientIso R r).symm

def torIso (M N : ModuleCat.{u} R) (P : ProjectiveResolution N) (i : ℕ) :
    (((Tor (ModuleCat R) i).obj (.of R (QuotSMulTop r M))).obj N) ≅
      (Parameter.QuotientComplex.complex R r
        (Parameter.TorSpecialization.tensorComplex R M N P)).homology i :=
  P.isoLeftDerivedObj (tensorLeft (.of R (QuotSMulTop r M))) i ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) i).mapIso
      ((NatIso.mapHomologicalComplex (tensorIso R r M) (ComplexShape.down ℕ)).app P.complex)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.QuotientTensor
