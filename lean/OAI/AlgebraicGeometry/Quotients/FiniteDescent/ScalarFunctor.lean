import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleBaseChangeComplex
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorProducts
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ShortComplexNatural

/-! # Scalar Functor -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarFunctor

noncomputable section

/-! The explicit tensor functor used in local algebra agrees with native
extension of scalars, including iterated extension to a residue field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Construction.ScalarFunctorComparison

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

omit [Algebra R S] in
def isoOfHom (f : R →+* S) : letI : Algebra R S := f.toAlgebra
    ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R S ≅ ModuleCat.extendScalars f := by
  letI : Algebra R S := f.toAlgebra
  refine NatIso.ofComponents (fun M => (LinearEquiv.refl S (S ⊗[R] M)).toModuleIso) ?_
  intro M N a
  apply ModuleCat.ExtendScalars.hom_ext (f := f)
  intro m
  rfl

def iso : ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R S ≅
    ModuleCat.extendScalars (algebraMap R S) := by
  have h : @ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R S _ _ (algebraMap R S).toAlgebra =
      ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R S :=
    congrArg (fun a : Algebra R S => @ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeFunctor R S _ _ a)
      (toAlgebra_algebraMap (R := R) (S := S))
  exact eqToIso h.symm ≪≫ isoOfHom R S (algebraMap R S)

variable {A : Type u} [CommRing A] (f : R →+* S) (g : S →+* A)

omit [Algebra R S] in
theorem iterated_quasiIso {C D : ShortComplex (ModuleCat.{u} R)} (a : C ⟶ D)
    [ShortComplex.QuasiIso ((ModuleCat.extendScalars (g.comp f)).mapShortComplex.map a)] :
    ShortComplex.QuasiIso ((ModuleCat.extendScalars g).mapShortComplex.map
      ((ModuleCat.extendScalars f).mapShortComplex.map a)) :=
  ShortComplexNatural.Construction.ShortComplexNaturalIso.quasiIso (ModuleCat.extendScalarsComp f g) a

omit [Algebra R S] in
theorem iterated_jointly {C T₁ T₂ : ShortComplex (ModuleCat.{u} R)} (r₁ : C ⟶ T₁) (r₂ : C ⟶ T₂)
    (hd : CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars (g.comp f)).mapShortComplex.map r₁)
      ((ModuleCat.extendScalars (g.comp f)).mapShortComplex.map r₂)) :
    CechBoundary.Construction.CechBoundaryTransport.JointlyDetects
      ((ModuleCat.extendScalars g).mapShortComplex.map ((ModuleCat.extendScalars f).mapShortComplex.map r₁))
      ((ModuleCat.extendScalars g).mapShortComplex.map ((ModuleCat.extendScalars f).mapShortComplex.map r₂)) :=
  ShortComplexNatural.Construction.ShortComplexNaturalIso.jointly (ModuleCat.extendScalarsComp f g) r₁ r₂ hd

end Construction.ScalarFunctorComparison

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ScalarFunctor
