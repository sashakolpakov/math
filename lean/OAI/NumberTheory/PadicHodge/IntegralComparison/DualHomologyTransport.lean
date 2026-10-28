import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology

/-! # Dual Homology Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport

noncomputable section

/-! Transport an additive duality isomorphism along a coefficient-linear
cohomology isomorphism. The reversal in the dual is explicit. -/

open _root_.CategoryTheory Opposite

universe u

variable (R : Type u) [CommRing R]

def dualGroup (M : ModuleCat.{u} R) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Module.Dual R M)

def dualIso {M N : ModuleCat.{u} R} (e : M ≅ N) : dualGroup R M ≅ dualGroup R N :=
  (forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapIso
    ((ExactModuleDualFunctor.functor R).mapIso e.op.symm)

def transport {A : AddCommGrpCat.{u}} {M N : ModuleCat.{u} R}
    (e : A ≅ dualGroup R M) (f : M ≅ N) : A ≅ dualGroup R N :=
  e ≪≫ dualIso R f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DualHomologyTransport
