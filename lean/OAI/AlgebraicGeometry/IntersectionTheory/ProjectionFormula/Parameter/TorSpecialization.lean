import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Resolution
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TensorComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ComplexEuler

/-! # Tor Specialization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorSpecialization

noncomputable section

/-! Native Tor over a regular parameter fiber is the homology of
the original tensor resolution reduced modulo the parameter. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] (r : R)
  (hregular : IsSMulRegular R r)
  (M N : ModuleCat.{u} R) (hN : IsSMulRegular N r)
  (P : ProjectiveResolution N)

def tensorComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

def torIso (i : ℕ) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
      (((Tor (ModuleCat (ScalarQuotient.Ring R r)) i).obj ((ScalarQuotient.quotient R r).obj M)).obj
        ((ScalarQuotient.quotient R r).obj N)) ≅
    (QuotientComplex.complex R r (tensorComplex R M N P)).homology i := by
  let U := ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))
  let Q := Resolution.resolution R r hregular N hN P
  let L := ((tensorLeft ((ScalarQuotient.quotient R r).obj M)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj Q.complex
  refine U.mapIso (Q.isoLeftDerivedObj (tensorLeft ((ScalarQuotient.quotient R r).obj M)) i) ≪≫
    ((L.sc i).mapHomologyIso U).symm ≪≫ ?_
  exact (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) i).mapIso
    ((NatIso.mapHomologicalComplex (TensorComparison.tensorIso R r M)
      (ComplexShape.down ℕ)).app P.complex)

include hregular hN in
theorem length (i : ℕ) :
    Module.length (ScalarQuotient.Ring R r)
      (((Tor (ModuleCat (ScalarQuotient.Ring R r)) i).obj ((ScalarQuotient.quotient R r).obj M)).obj
        ((ScalarQuotient.quotient R r).obj N)) =
    Module.length R
      ((QuotientComplex.complex R r (tensorComplex R M N P)).homology i) := by
  let T := (((Tor (ModuleCat (ScalarQuotient.Ring R r)) i).obj ((ScalarQuotient.quotient R r).obj M)).obj
    ((ScalarQuotient.quotient R r).obj N))
  let : Module R T := Module.compHom T (algebraMap R (ScalarQuotient.Ring R r))
  let : IsScalarTower R (ScalarQuotient.Ring R r) T := IsScalarTower.of_compHom R (ScalarQuotient.Ring R r) T
  have heq : Module.length R
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj T) =
      Module.length (ScalarQuotient.Ring R r) T :=
    Module.length_eq_of_surjective (M := T) Ideal.Quotient.mk_surjective
  exact heq.symm.trans (torIso R r hregular M N hN P i).toLinearEquiv.length_eq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorSpecialization
