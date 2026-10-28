import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeSheafPairing

/-! # Opposite Sheaf Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeSheafAnnihilator.Construction.CartierCoordinates

noncomputable section

/-!
The actual embedded opposite subgroup is the annihilator of the chosen
subgroup under the source character pairing. Double annihilation and
arbitrary base change apply to these native kernels, with the original
source inclusion retained.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] CartierSheafKernels.Construction.representedFppfAbMap_mono

variable {k : Type u} [Field k]
variable {G H B : Grp (Over (Spec (.of k)))}
variable [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj B.X]
variable (P : CartierModel.Construction.CartierCoordinates (.of k) G) (Q : CartierModel.Construction.CartierCoordinates (.of k) H)
variable (i : H ⟶ G) (e : B ≅ P.dualGroup)

local instance : IsCommMonObj P.dualGroup.X := P.dualGroup_commutative
local instance : IsCommMonObj Q.dualGroup.X := Q.dualGroup_commutative

omit [IsCommMonObj G.X] [IsCommMonObj H.X] in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOppositeRestriction_eq :
    P.representedOppositeRestriction Q i e =
      (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso e).hom ≫ P.representedRestriction Q i := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro b
  exact congrArg ULift.up
    (Category.assoc (show T.unop ⟶ B.X from b.down) e.hom.hom.hom
      (P.restriction Q i).hom.hom).symm

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceCharacterIso_restriction :
    P.representedOppositeRestriction Q i e ≫ Q.representedCartierDualIso.hom =
      (P.sourceCharacterIso e).hom ≫
        (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op := by
  let a := (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso e).hom
  let b := P.representedRestriction Q i
  let c := Q.representedCartierDualIso.hom
  let d := (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i).op
  exact (congrArg (fun z => z ≫ c) (P.representedOppositeRestriction_eq Q i e)).trans
    ((Category.assoc a b c).trans
      ((congrArg (fun z => a ≫ z) (P.representedCartierDualIso_restriction Q i)).trans
        (Category.assoc a P.representedCartierDualIso.hom d).symm))

variable [Mono i.hom.hom]

/-- Annihilation through the source Cartier identification produces
exactly the native opposite inclusion already used in the full kernel. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceSheafPairing_annihilator :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator (P.sourceSheafPairing e) (CartierModel.Construction.CartierCoordinates.representedSubgroup i) =
      Subobject.mk (P.representedOppositeInclusion Q i e) := by
  let D := CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))
  let a := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i
  let h := Subobject.underlyingIso a
  have hh : h.hom ≫ a = (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk a
  let c := Q.representedCartierDualIso.hom ≫ D.map h.hom.op
  have : IsIso c := (Q.representedCartierDualIso ≪≫ D.mapIso h.op).isIso_hom
  have hmap : (P.sourceCharacterIso e).hom ≫ D.map (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow.op =
      P.representedOppositeRestriction Q i e ≫ c := by
    have hd : D.map (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow.op = D.map a.op ≫ D.map h.hom.op :=
      (congrArg (fun z : (CartierModel.Construction.CartierCoordinates.representedSubgroup i : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k))) ⟶
        CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G => D.map z.op) hh.symm).trans
          ((congrArg D.map (show (h.hom ≫ a).op = a.op ≫ h.hom.op from op_comp)).trans
            (D.map_comp a.op h.hom.op))
    exact (congrArg (fun z => (P.sourceCharacterIso e).hom ≫ z) hd).trans
      ((Category.assoc (P.sourceCharacterIso e).hom (D.map a.op) (D.map h.hom.op)).symm.trans
        ((congrArg (fun z => z ≫ D.map h.hom.op)
          (P.sourceCharacterIso_restriction Q i e).symm).trans
            (Category.assoc (P.representedOppositeRestriction Q i e) Q.representedCartierDualIso.hom
              (D.map h.hom.op))))
  change kernelSubobject ((P.sourceSheafPairing e).rightAdjoint ≫ D.map (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow.op) = _
  rw [P.sourceSheafPairing_rightAdjoint e, hmap]
  exact (kernelSubobject_comp_mono (P.representedOppositeRestriction Q i e) c).trans
    (P.representedOpposite_subobject Q i e).symm

/-- The second annihilator is the original chosen native subgroup. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOpposite_double :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator (P.sourceSheafPairing e).flip
      (Subobject.mk (P.representedOppositeInclusion Q i e)) = CartierModel.Construction.CartierCoordinates.representedSubgroup i := by
  rw [← P.sourceSheafPairing_annihilator Q i e]
  exact CartierDuality.PolarizedTorsion.Construction.annihilator_double (P.sourceSheafPairing e) (CartierModel.Construction.CartierCoordinates.representedSubgroup i)
    (P.sourceSheafPairing_isPerfect e) P.represented_finiteLocallyFree
      (Q.representedSubgroup_finiteLocallyFree i)

/-- The embedded opposite kernel commutes with every base change,
using the canonical base change of the original character pairing. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOpposite_baseChange (T : Scheme.{u}) (f : T ⟶ Spec (.of k)) :
    CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangeSubobject f (Subobject.mk (P.representedOppositeInclusion Q i e)) =
      CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangePairing f (P.sourceSheafPairing e))
        (CartierDuality.AnnihilatorBaseChange.Construction.Schemes.baseChangeSubobject f (CartierModel.Construction.CartierCoordinates.representedSubgroup i)) := by
  rw [← P.sourceSheafPairing_annihilator Q i e]
  exact CartierDuality.AnnihilatorBaseChange.Construction.Schemes.sheafAnnihilator_baseChange f (P.sourceSheafPairing e) (CartierModel.Construction.CartierCoordinates.representedSubgroup i)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeSheafAnnihilator.Construction.CartierCoordinates
