import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BaseChangeComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorProducts

/-! # Functor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctorComparison.ScalarFunctorComparison

noncomputable section

/-! The explicit tensor functor used in local algebra agrees with native
extension of scalars, including iterated extension to a residue field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

omit [Algebra R S] in
def isoOfHom (f : R →+* S) : letI : Algebra R S := f.toAlgebra
    Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S ≅ ModuleCat.extendScalars f := by
  letI : Algebra R S := f.toAlgebra
  refine NatIso.ofComponents (fun M => (LinearEquiv.refl S (S ⊗[R] M)).toModuleIso) ?_
  intro M N a
  apply ModuleCat.ExtendScalars.hom_ext (f := f)
  intro m
  rfl

def iso : Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S ≅
    ModuleCat.extendScalars (algebraMap R S) := by
  have h : @Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S _ _ (algebraMap R S).toAlgebra =
      Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S :=
    congrArg (fun a : Algebra R S => @Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R S _ _ a)
      (toAlgebra_algebraMap (R := R) (S := S))
  exact eqToIso h.symm ≪≫ isoOfHom R S (algebraMap R S)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.FunctorComparison.ScalarFunctorComparison
