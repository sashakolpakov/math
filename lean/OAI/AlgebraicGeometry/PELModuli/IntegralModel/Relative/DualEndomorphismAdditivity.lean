import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions

/-! # Dual Endomorphism Additivity -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualEndomorphismAdditivity

noncomputable section

/-! The actual dual construction is additive on the endomorphism ring
of an arbitrary abelian family over a reduced noetherian base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PoincareEq.RelativePoincareClasses

variable {S : Scheme.{0}} [IsReduced S] [IsNoetherian S] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def relativeDualGroupEnd (r : Finite.Actions.GroupEndRing A) : Finite.Actions.GroupEndRing D.abelian :=
  letI := DualFamilyMorphism.dualPicardPullback_preserves_given_group D D (r.hom A)
  Finite.Actions.GroupEndRing.ofHom D.abelian (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D (r.hom A))

theorem relativeDualGroupEnd_leftClass (r : Finite.Actions.GroupEndRing A) :
    PoincareEq.RelativePoincareClasses.leftOperatorClass D ((relativeDualGroupEnd D r).hom D.abelian) = PoincareEq.RelativePoincareClasses.rightOperatorClass D (r.hom A) :=
  DualPoincare.dualPicardPullback_actual_poincare_relative D D (r.hom A)

theorem relativeDualGroupEnd_add (r s : Finite.Actions.GroupEndRing A) :
    relativeDualGroupEnd D (r + s) = relativeDualGroupEnd D r + relativeDualGroupEnd D s := by
  apply Finite.Actions.GroupEndRing.ext
  apply PoincareEq.RelativePoincareClasses.leftOperatorClass_injective D
  rw [Finite.Actions.GroupEndRing.hom_add, PoincareEq.RelativePoincareClasses.leftOperatorClass_mul, relativeDualGroupEnd_leftClass,
    relativeDualGroupEnd_leftClass, relativeDualGroupEnd_leftClass, Finite.Actions.GroupEndRing.hom_add, PoincareEq.RelativePoincareClasses.rightOperatorClass_mul]

theorem relativeDualGroupEnd_zero : relativeDualGroupEnd D 0 = 0 := by
  have h := relativeDualGroupEnd_add D 0 0
  rw [zero_add] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

def relativeDualGroupEndAddHom : Finite.Actions.GroupEndRing A →+ Finite.Actions.GroupEndRing D.abelian where
  toFun := relativeDualGroupEnd D
  map_zero' := relativeDualGroupEnd_zero D
  map_add' := relativeDualGroupEnd_add D

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DualEndomorphismAdditivity
