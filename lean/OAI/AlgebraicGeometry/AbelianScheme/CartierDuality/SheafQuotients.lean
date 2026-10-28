import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTranspose
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Sheaf Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients.Construction

noncomputable section

/-!
# CartierDuality: actual fppf quotients and annihilator sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u v

namespace CommutativeSheaves

/-- Zero morphisms in multiplicative notation are the trivial homomorphisms. -/
instance commGrpZeroMorphisms : HasZeroMorphisms CommGrpCat.{u} where
  zero X Y := ⟨CommGrpCat.ofHom 1⟩
  comp_zero f Z := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    rfl
  zero_comp := by
    intro X Y Z f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact f.hom.map_one

/-- Colimits of commutative groups exist in multiplicative notation,
by the equivalence with additive commutative groups. -/
instance commGrpColimits : HasColimitsOfSize.{u, u} CommGrpCat.{u} :=
  Adjunction.has_colimits_of_equivalence commGroupAddCommGroupEquivalence.functor

end CommutativeSheaves

namespace AnnihilatorComparison

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {K R H Q : C} (r : K ⟶ R) (d : R ⟶ H) (q : Q ⟶ R)
    (w : q ≫ d = 0) (hq : IsLimit (KernelFork.ofι q w)) [HasKernel (r ≫ d)]

/-- The kernel of the composite maps canonically into any chosen kernel of the last map. -/
def toKernel : (kernelSubobject (r ≫ d) : C) ⟶ Q :=
  hq.lift (KernelFork.ofι ((kernelSubobject (r ≫ d)).arrow ≫ r)
    ((Category.assoc _ r d).trans (kernelSubobject_arrow_comp (r ≫ d))))

/-- The canonical map respects the original inclusions. -/
theorem toKernel_fac : toKernel r d q w hq ≫ q = (kernelSubobject (r ≫ d)).arrow ≫ r :=
  Fork.IsLimit.lift_ι hq

variable [IsIso r]

/-- An invertible first map yields the inverse comparison of kernels. -/
def fromKernel : Q ⟶ (kernelSubobject (r ≫ d) : C) :=
  factorThruKernelSubobject (r ≫ d) (q ≫ inv r) (by simpa using w)

/-- The inverse comparison respects the original inclusions. -/
theorem fromKernel_fac : fromKernel r d q w ≫ (kernelSubobject (r ≫ d)).arrow = q ≫ inv r :=
  factorThruKernelSubobject_comp_arrow _ _ _

/-- The canonical kernel comparison is an isomorphism if the first map is invertible. -/
def iso : (kernelSubobject (r ≫ d) : C) ≅ Q where
  hom := toKernel r d q w hq
  inv := fromKernel r d q w
  hom_inv_id := by
    apply (cancel_mono (kernelSubobject (r ≫ d)).arrow).mp
    rw [Category.assoc, fromKernel_fac, ← Category.assoc, toKernel_fac]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply Fork.IsLimit.hom_ext hq
    change (fromKernel r d q w ≫ toKernel r d q w hq) ≫ q = (𝟙 Q) ≫ q
    rw [Category.assoc, toKernel_fac, ← Category.assoc, fromKernel_fac]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

end AnnihilatorComparison

namespace Schemes

/-- Actual sheaf quotients exist in the common fppf-sheaf universe. -/
instance fppfAbHasCokernels (S : Scheme.{u}) : HasCokernels (CommutativeSheavesAb.Construction.Schemes.FppfAb S) := inferInstance

/-- The actual Cartier-dual functor sends trivial morphisms to trivial morphisms. -/
instance cartierDualSheafFunctor_preservesZero (S : Scheme.{u}) :
    Functor.PreservesZeroMorphisms (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) where
  map_zero := by
    intro G H
    apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
    apply NatTrans.ext
    funext T
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro χ
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact (χ.app U).hom.map_one

/-- The fppf sheaf quotient by a subobject is its actual categorical cokernel. -/
def sheafQuotient {S : Scheme.{u}} {G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (H : Subobject G) : CommutativeSheavesAb.Construction.Schemes.FppfAb S :=
  cokernel H.arrow

/-- The annihilator is the kernel of restriction of the pairing's
right adjoint to the actual subgroup sheaf. -/
def sheafAnnihilator {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K)
    (H : Subobject G) : Subobject K :=
  kernelSubobject (e.rightAdjoint ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op)

/-- The character of a quotient is trivial on the quotient's defining subgroup. -/
theorem dualCokernel_condition {S : Scheme.{u}} {H G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (i : H ⟶ G) :
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (cokernel.π i).op ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map i.op = 0 := by
  rw [← Functor.map_comp, ← op_comp, cokernel.condition, op_zero, Functor.map_zero]

/-- The dual of an actual sheaf cokernel is the kernel of character
restriction. This follows from the proved self-adjunction. -/
def dualCokernelIsKernel {S : Scheme.{u}} {H G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (i : H ⟶ G) :
    IsLimit (KernelFork.ofι ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (cokernel.π i).op)
      (dualCokernel_condition i)) := by
  let : (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).IsRightAdjoint := (SheafTranspose.Construction.Schemes.cartierSheafAdjunction S).isRightAdjoint
  have h := CokernelCofork.IsColimit.ofπOp (cokernel.π i) (cokernel.condition i) (cokernelIsCokernel i)
  exact isLimitForkMapOfIsLimit' (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S) _ h

/-- The actual character sheaf of a quotient is canonically
isomorphic to the kernel of restriction to its subgroup. -/
def quotientDualKernelIso {S : Scheme.{u}} {G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (H : Subobject G) :
    CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (sheafQuotient H) ≅ kernel ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op) :=
  (dualCokernelIsKernel H.arrow).conePointUniqueUpToIso
    (limit.isLimit (parallelPair ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op) 0))

/-- Restricting the pairing to the annihilator kills the subgroup. -/
theorem annihilator_condition {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K)
    (H : Subobject G) :
    ((sheafAnnihilator e H).arrow ≫ e.rightAdjoint) ≫
      (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op = 0 :=
  (Category.assoc (sheafAnnihilator e H).arrow e.rightAdjoint
    ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op)).trans (kernelSubobject_arrow_comp _)

/-- Every pairing gives a canonical morphism from its annihilator to
the character sheaf of the quotient, before any perfection assumption. -/
def annihilatorToQuotientDual {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K)
    (H : Subobject G) : (sheafAnnihilator e H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) ⟶ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (sheafQuotient H) :=
  AnnihilatorComparison.toKernel e.rightAdjoint ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op)
    ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (cokernel.π H.arrow).op) (dualCokernel_condition H.arrow)
      (dualCokernelIsKernel H.arrow)

/-- The canonical annihilator-to-quotient-dual map has the exact
restriction formula determined by the original pairing. -/
theorem annihilatorToQuotientDual_fac {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K)
    (H : Subobject G) :
    annihilatorToQuotientDual e H ≫ (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (cokernel.π H.arrow).op =
      (sheafAnnihilator e H).arrow ≫ e.rightAdjoint :=
  AnnihilatorComparison.toKernel_fac e.rightAdjoint ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op)
    ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (cokernel.π H.arrow).op) (dualCokernel_condition H.arrow)
      (dualCokernelIsKernel H.arrow)

/-- Under a perfect pairing, the canonical annihilator-to-quotient-dual
map is an isomorphism of the actual fppf sheaves. -/
def annihilatorQuotientDualIso {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K)
    (H : Subobject G) (he : e.IsPerfect) :
    (sheafAnnihilator e H : CommutativeSheavesAb.Construction.Schemes.FppfAb S) ≅ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (sheafQuotient H) := by
  let : IsIso e.rightAdjoint := he.2
  exact AnnihilatorComparison.iso e.rightAdjoint ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map H.arrow.op)
    ((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (cokernel.π H.arrow).op) (dualCokernel_condition H.arrow)
      (dualCokernelIsKernel H.arrow)

/-- The canonical quotient-dual comparison is invertible for a perfect pairing. -/
theorem annihilatorToQuotientDual_isIso {S : Scheme.{u}} {G K : CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : SheafEvaluation.Construction.Schemes.BilinearPairing G K) (H : Subobject G) (he : e.IsPerfect) :
    IsIso (annihilatorToQuotientDual e H) :=
  (annihilatorQuotientDualIso e H he).isIso_hom

end Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafQuotients.Construction
