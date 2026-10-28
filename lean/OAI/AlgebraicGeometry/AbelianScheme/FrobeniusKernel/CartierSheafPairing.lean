import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierSheafKernels

/-! # Cartier Sheaf Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-!
Canonical character evaluation for the native coordinate dual is perfect.
Its annihilator is the actual embedded opposite kernel, so CartierDuality's double
annihilator theorem applies directly to the constructed native subgroups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] CartierSheafKernels.Construction.representedFppfAbMap_mono

variable {R : CommRingCat.{u}} {G H : Grp (Over (Spec R))}
variable [IsCommMonObj G.X] [IsCommMonObj H.X]
variable (P : CartierModel.Construction.CartierCoordinates R G) (Q : CartierModel.Construction.CartierCoordinates R H) (i : H ⟶ G)

include P in
/-- The native coordinate presentation exhibits finite local freeness
of its represented commutative sheaf. -/
theorem CartierModel.Construction.CartierCoordinates.represented_finiteLocallyFree : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb (Spec R) (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G) :=
  ⟨G, inferInstance, P.group_finiteLocallyFree.1, P.group_finiteLocallyFree.2.1,
    P.group_finiteLocallyFree.2.2, ⟨Iso.refl _⟩⟩

/-- Evaluation of a native character, expressed as a sheaf pairing. -/
def CartierModel.Construction.CartierCoordinates.evaluationPairing : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G)
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) P.dualGroup) :=
  (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk P.representedCartierDualIso.hom).flip

theorem CartierModel.Construction.CartierCoordinates.evaluationPairing_rightAdjoint :
    P.evaluationPairing.rightAdjoint = P.representedCartierDualIso.hom :=
  congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint
    (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk P.representedCartierDualIso.hom).flip_flip

/-- Perfection follows from canonical biduality and the proved native
character representation; it is not a pairing premise. -/
theorem CartierModel.Construction.CartierCoordinates.evaluationPairing_isPerfect : P.evaluationPairing.IsPerfect := by
  have : IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G)) :=
    (CartierDuality.PolarizedTorsion.Construction.cartier_duality _ P.represented_finiteLocallyFree).2.2.1
  constructor
  · change IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G) ≫
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec R)).map P.representedCartierDualIso.hom.op)
    exact (asIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G)) ≪≫
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec R)).mapIso P.representedCartierDualIso.op).isIso_hom
  · rw [P.evaluationPairing_rightAdjoint]
    infer_instance

theorem CartierModel.Construction.CartierCoordinates.evaluationPairing_value (T : Over (Spec R)) (d : T ⟶ P.dualGroup.X) (x : T ⟶ G.X) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G) T
      (P.evaluationPairing.rightAdjoint.hom.app (op T) (ULift.up d)) (ULift.up x) =
        ULift.up ((P.pointsEquiv T d).app (op (Over.mk (𝟙 T))) x) := by
  rw [P.evaluationPairing_rightAdjoint]
  exact P.representedCartierDualIso_value T d x

variable [Mono i.hom.hom]

/-- The original chosen native subgroup as an embedded fppf subgroup. -/
abbrev CartierModel.Construction.CartierCoordinates.representedSubgroup : Subobject (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G) :=
  Subobject.mk (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)

/-- Native character annihilation and sheaf annihilation give the same
embedded subgroup, including the original inclusion map. -/
theorem CartierModel.Construction.CartierCoordinates.evaluationPairing_annihilator :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator P.evaluationPairing (CartierModel.Construction.CartierCoordinates.representedSubgroup i) =
      Subobject.mk (P.representedAnnihilatorInclusion Q i) := by
  let D := CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor (Spec R)
  let a := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i
  let e := Subobject.underlyingIso a
  have he : e.hom ≫ a = (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk a
  have : IsIso (D.map e.hom.op) := D.map_isIso e.hom.op
  let c := Q.representedCartierDualIso.hom ≫ D.map e.hom.op
  have : IsIso c := (Q.representedCartierDualIso ≪≫ D.mapIso e.op).isIso_hom
  have hmap : P.representedCartierDualIso.hom ≫ D.map (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow.op =
      P.representedRestriction Q i ≫ c := by
    have hd : D.map (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow.op = D.map a.op ≫ D.map e.hom.op :=
      (congrArg (fun z : (CartierModel.Construction.CartierCoordinates.representedSubgroup i : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec R)) ⟶
        CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec R) G => D.map z.op) he.symm).trans
          ((congrArg D.map (show (e.hom ≫ a).op = a.op ≫ e.hom.op from op_comp)).trans (D.map_comp a.op e.hom.op))
    exact (congrArg (fun z => P.representedCartierDualIso.hom ≫ z) hd).trans
      ((Category.assoc P.representedCartierDualIso.hom (D.map a.op) (D.map e.hom.op)).symm.trans
        ((congrArg (fun z => z ≫ D.map e.hom.op)
          (P.representedCartierDualIso_restriction Q i).symm).trans
            (Category.assoc (P.representedRestriction Q i) Q.representedCartierDualIso.hom
              (D.map e.hom.op))))
  change kernelSubobject (P.evaluationPairing.rightAdjoint ≫ D.map (CartierModel.Construction.CartierCoordinates.representedSubgroup i).arrow.op) = _
  rw [P.evaluationPairing_rightAdjoint, hmap]
  exact (kernelSubobject_comp_mono (P.representedRestriction Q i)
    c).trans
      (P.representedAnnihilator_subobject Q i).symm

include Q in
/-- The represented native subgroup retains its actual finite locally
free model rather than introducing a representability assumption. -/
theorem CartierModel.Construction.CartierCoordinates.representedSubgroup_finiteLocallyFree :
    CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb (Spec R) (CartierModel.Construction.CartierCoordinates.representedSubgroup i : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec R)) :=
  Q.represented_finiteLocallyFree.of_iso (Subobject.underlyingIso (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i)).symm

/-- Annihilating the constructed opposite kernel recovers the original
chosen subgroup, as an equality of embedded fppf subgroups. -/
theorem CartierModel.Construction.CartierCoordinates.representedAnnihilator_double :
    CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator P.evaluationPairing.flip
      (Subobject.mk (P.representedAnnihilatorInclusion Q i)) = CartierModel.Construction.CartierCoordinates.representedSubgroup i := by
  rw [← P.evaluationPairing_annihilator Q i]
  exact CartierDuality.PolarizedTorsion.Construction.annihilator_double P.evaluationPairing (CartierModel.Construction.CartierCoordinates.representedSubgroup i)
    P.evaluationPairing_isPerfect P.represented_finiteLocallyFree
      (Q.representedSubgroup_finiteLocallyFree i)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
