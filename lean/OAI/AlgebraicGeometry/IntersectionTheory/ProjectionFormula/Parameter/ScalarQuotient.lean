import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.Extension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex
import Mathlib.RingTheory.Regular.Free
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Scalar Quotient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

noncomputable section

/-! The parameter quotient functor with values in modules over the
quotient ring. Its projectivity follows from the actual tensor-product
description of the quotient. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R] (r : R)

abbrev Ring := R ⧸ Ideal.span {r}

def quotient : ModuleCat.{u} R ⥤ ModuleCat.{u} (Ring R r) where
  obj M := .of (Ring R r) (QuotSMulTop r M)
  map f := ModuleCat.ofHom ((QuotSMulTop.map r f.hom).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective)
  map_id M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (QuotSMulTop.map_id r M) x
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (QuotSMulTop.map_comp r g.hom f.hom) x

instance : (quotient R r).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun ((QuotSMulTop.map r).map_add f.hom g.hom) x

def baseChangeEquiv (M : ModuleCat.{u} R) :
    QuotSMulTop r M ≃ₗ[Ring R r] Ring R r ⊗[R] M :=
  (QuotSMulTop.equivQuotTensor r M).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

instance : (quotient R r).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    let : Projective M := hM
    let : Module.Projective R M := inferInstance
    let : Module.Projective (Ring R r) (QuotSMulTop r M) :=
      Module.Projective.of_equiv (baseChangeEquiv R r M).symm
    exact inferInstanceAs (Projective (ModuleCat.of (Ring R r) (QuotSMulTop r M)))

def restrictionIso : quotient R r ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})) ≅
    QuotientComplex.quotient R r :=
  NatIso.ofComponents (fun M => (LinearEquiv.refl R (QuotSMulTop r M)).toModuleIso)
    (by intro M N f; rfl)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient
