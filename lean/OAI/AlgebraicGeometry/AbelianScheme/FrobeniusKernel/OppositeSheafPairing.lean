import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierSheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PairedKernels

/-! # Opposite Sheaf Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeSheafPairing.Construction.CartierCoordinates

noncomputable section

/-!
Transport canonical character evaluation through the actual source
Cartier identification. The native opposite inclusion is proved to be
its sheaf annihilator, with double annihilation and arbitrary base change.
This comparison does not identify the source character identification
with the Poincare-induced Weil pairing.
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

def _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceCharacterIso : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) B ≅
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G) :=
  CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso e ≪≫ P.representedCartierDualIso

/-- The source identification carries its literal character pairing. -/
def _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceSheafPairing : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G)
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) B) :=
  (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk (P.sourceCharacterIso e).hom).flip

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceSheafPairing_rightAdjoint :
    (P.sourceSheafPairing e).rightAdjoint = (P.sourceCharacterIso e).hom :=
  congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk (P.sourceCharacterIso e).hom).flip_flip

theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceSheafPairing_isPerfect : (P.sourceSheafPairing e).IsPerfect := by
  have : IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G)) :=
    (CartierDuality.PolarizedTorsion.Construction.cartier_duality _ P.represented_finiteLocallyFree).2.2.1
  constructor
  · change IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G) ≫
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).map (P.sourceCharacterIso e).hom.op)
    exact (asIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G)) ≪≫
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec (.of k))).mapIso (P.sourceCharacterIso e).op).isIso_hom
  · rw [P.sourceSheafPairing_rightAdjoint e]
    infer_instance

/-- The transported sheaf pairing evaluates through the original
opposite-block Cartier isomorphism on every native point. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.sourceSheafPairing_value (T : Over (Spec (.of k))) (b : T ⟶ B.X) (x : T ⟶ G.X) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) G) T
      ((P.sourceSheafPairing e).rightAdjoint.hom.app (op T) (ULift.up b)) (ULift.up x) =
        ULift.up ((P.pointsEquiv T (b ≫ e.hom.hom.hom)).app (op (Over.mk (𝟙 T))) x) := by
  rw [P.sourceSheafPairing_rightAdjoint e]
  exact P.representedCartierDualIso_value T (b ≫ e.hom.hom.hom) x

instance _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.oppositeInclusion_mono : Mono (P.oppositeInclusion Q i e).hom.hom := by
  have : IsIso e.inv.hom.hom := ((Grp.forget _).mapIso e).isIso_inv
  change Mono ((P.annihilatorInclusion Q i).hom.hom ≫ e.inv.hom.hom)
  infer_instance

abbrev _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOppositeInclusion : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (P.annihilatorGroup Q i) ⟶
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) B := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (P.oppositeInclusion Q i e)

abbrev _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOppositeRestriction : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) B ⟶
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) Q.dualGroup := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (e.hom ≫ P.restriction Q i)

omit [IsCommMonObj G.X] [IsCommMonObj H.X] in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOpposite_condition :
    P.representedOppositeInclusion Q i e ≫ P.representedOppositeRestriction Q i e = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro a
  let a' : T.unop ⟶ (P.annihilatorGroup Q i).X := a.down
  change ULift.up (a' ≫ ((P.annihilatorInclusion Q i).hom.hom ≫ e.inv.hom.hom) ≫
    (e.hom.hom.hom ≫ (P.restriction Q i).hom.hom)) = ULift.up 1
  apply congrArg ULift.up
  have he : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 P.dualGroup.X :=
    ((Grp.forget _).mapIso e).inv_hom_id
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom, he,
    Category.id_comp, P.annihilatorInclusion_restriction Q i, MonObj.comp_one]

/-- The original opposite inclusion is the kernel of the transported
character restriction, in the category of commutative fppf sheaves. -/
def _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOppositeIsLimit :
    IsLimit (KernelFork.ofι (P.representedOppositeInclusion Q i e)
      (P.representedOpposite_condition Q i e)) := by
  apply CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints
  intro T b hb
  let b' : T ⟶ B.X := b.down
  have hb' : (b' ≫ e.hom.hom.hom) ≫ (P.restriction Q i).hom.hom = 1 :=
    (Category.assoc _ _ _).trans (congrArg ULift.down hb)
  obtain ⟨a, ha, _⟩ := (P.annihilator_universal Q i T (b' ≫ e.hom.hom.hom)).mp
    ((P.annihilator_condition Q i T _).mp hb')
  refine ⟨ULift.up a, ?_⟩
  change ULift.up (a ≫ ((P.annihilatorInclusion Q i).hom.hom ≫ e.inv.hom.hom)) = ULift.up b'
  apply congrArg ULift.up
  have he : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 B.X := ((Grp.forget _).mapIso e).hom_inv_id
  exact (Category.assoc a (P.annihilatorInclusion Q i).hom.hom e.inv.hom.hom).symm.trans
    ((congrArg (fun z => z ≫ e.inv.hom.hom) ha).trans
      ((Category.assoc b' e.hom.hom.hom e.inv.hom.hom).trans
        ((congrArg (fun z => b' ≫ z) he).trans (Category.comp_id b'))))

omit [IsCommMonObj G.X] [IsCommMonObj H.X] in
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates.representedOpposite_subobject :
    Subobject.mk (P.representedOppositeInclusion Q i e) =
      kernelSubobject (P.representedOppositeRestriction Q i e) := by
  let a := (P.representedOppositeIsLimit Q i e).conePointUniqueUpToIso
    (kernelIsKernel (P.representedOppositeRestriction Q i e))
  apply Subobject.mk_eq_mk_of_comm _ _ a
  exact IsLimit.conePointUniqueUpToIso_hom_comp (P.representedOppositeIsLimit Q i e)
    (kernelIsKernel _) WalkingParallelPair.zero

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OppositeSheafPairing.Construction.CartierCoordinates
