import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareOperators
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualPoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualGroupMorphism

/-! # Dual Endomorphism Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualEndomorphismAdditivity

noncomputable section

/-! The actual dual construction is additive on the endomorphism ring
of an arbitrary abelian family over a noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.Actions
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PoincareOperators.RelativePoincareClasses

variable {S : Scheme.{0}} [IsNoetherian S] {g : ℕ}
  {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : HilbertConstruction.Dual.Data.DualAbelianData A)

def relativeDualGroupEnd (r : PELModuli.IntegralModel.Finite.Actions.GroupEndRing A) : PELModuli.IntegralModel.Finite.Actions.GroupEndRing D.abelian :=
  letI := DualGroupMorphism.dualPicardPullback_preserves_given_group D D (r.hom A)
  PELModuli.IntegralModel.Finite.Actions.GroupEndRing.ofHom D.abelian (Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback D D (r.hom A))

theorem relativeDualGroupEnd_leftClass (r : PELModuli.IntegralModel.Finite.Actions.GroupEndRing A) :
    PoincareOperators.RelativePoincareClasses.leftOperatorClass D ((relativeDualGroupEnd D r).hom D.abelian) = PoincareOperators.RelativePoincareClasses.rightOperatorClass D (r.hom A) :=
  DualPoincare.dualPicardPullback_actual_poincare_relative D D (r.hom A)

theorem relativeDualGroupEnd_add (r s : PELModuli.IntegralModel.Finite.Actions.GroupEndRing A) :
    relativeDualGroupEnd D (r + s) = relativeDualGroupEnd D r + relativeDualGroupEnd D s := by
  apply PELModuli.IntegralModel.Finite.Actions.GroupEndRing.ext
  apply PoincareOperators.RelativePoincareClasses.leftOperatorClass_injective D
  rw [PELModuli.IntegralModel.Finite.Actions.GroupEndRing.hom_add, PoincareOperators.RelativePoincareClasses.leftOperatorClass_mul, relativeDualGroupEnd_leftClass,
    relativeDualGroupEnd_leftClass, relativeDualGroupEnd_leftClass, PELModuli.IntegralModel.Finite.Actions.GroupEndRing.hom_add, PoincareOperators.RelativePoincareClasses.rightOperatorClass_mul]

theorem relativeDualGroupEnd_zero : relativeDualGroupEnd D 0 = 0 := by
  have h := relativeDualGroupEnd_add D 0 0
  rw [zero_add] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

def relativeDualGroupEndAddHom : PELModuli.IntegralModel.Finite.Actions.GroupEndRing A →+ PELModuli.IntegralModel.Finite.Actions.GroupEndRing D.abelian where
  toFun := relativeDualGroupEnd D
  map_zero' := relativeDualGroupEnd_zero D
  map_add' := relativeDualGroupEnd_add D

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.DualEndomorphismAdditivity
