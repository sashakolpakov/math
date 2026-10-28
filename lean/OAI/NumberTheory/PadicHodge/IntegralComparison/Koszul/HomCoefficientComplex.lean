import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KoszulHomotopy

/-! # Hom Coefficient Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomCoefficientComplex

noncomputable section

/-! The native exterior Koszul Hom presheaf is the ordinary additive
Hom functor applied to the original Koszul chain complex. -/
open _root_.CategoryTheory Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {C : Type u} [Category C]
  (R : Type u) [CommRing R] (V : Type u) [AddCommGroup V] [Module R V]
  (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (l : Module.Dual R V)

def iso :
    HomCoefficientFunctor.complex R P (Exterior.KoszulComplex.complex R V l) ≅
      HomPresheaf.complex R V P l :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have h : i + 1 = j := hij
    subst j
    apply NatTrans.ext
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    dsimp only [HomCoefficientFunctor.complex, Functor.mapHomologicalComplex_obj_d,
      HomologicalComplex.op_d, HomCoefficientFunctor.functor,
      HomCoefficientFunctor.precomp]
    symm
    change (show (⋀[R]^i V) →ₗ[R] P.obj a from φ)
      ((Exterior.KoszulComplex.complex R V l).d (i + 1) i x) = _
    rw [Exterior.KoszulHomotopy.complex_d]
    dsimp only [HomPresheaf.complex]
    rw [CochainComplex.of_d]
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.HomCoefficientComplex
