import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafCharacterComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EvaluationBaseChange

/-! # Sheaf Bidual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: transferring native bidual perfection to the actual fppf-sheaf bidual
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

variable {S : Scheme.{u}}

/-- Cancellation of a sheaf isomorphism on a section. -/
theorem SheafBidual.Construction.Schemes.sheafIso_hom_inv_apply {F K : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (e : F ≅ K) (T : Over S)
    (x : F.obj.obj (Opposite.op T)) :
    e.inv.hom.app (Opposite.op T) (e.hom.hom.app (Opposite.op T) x) = x :=
  congrArg (fun a : F ⟶ F => a.hom.app (Opposite.op T) x) e.hom_inv_id

/-- Native bidual perfection supplies an isomorphism to the actual
double character sheaf, through the canonical representation comparisons. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedBidualIso {G : Grp (Over S)} [IsCommMonObj G.X]
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    [IsIso (D.bidualEvaluation E)] :
    CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G ≅ CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) := by
  let : IsCommMonObj D.dual.X := D.commutative
  let : IsCommMonObj E.dual.X := E.commutative
  exact SheafBaseChange.Construction.Schemes.representedFppfAbIso (asIso (D.bidualEvaluation E)) ≪≫ E.representedCartierDualIso ≪≫
    (CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso D.representedCartierDualIso.symm.op

/-- The transported bidual isomorphism has precisely the transposed
native evaluation values. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedBidualIso_pairing
    {G : Grp (Over S)} [IsCommMonObj G.X] (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) [IsIso (D.bidualEvaluation E)]
    (T : Over S) (x : T ⟶ G.X) (d : T ⟶ D.dual.X) :
    SheafEvaluation.Construction.Schemes.sheafCharacterValue (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) T
      ((D.representedBidualIso E).hom.hom.app (Opposite.op T) (ULift.up x))
      (D.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up d)) =
    SheafEvaluation.Construction.Schemes.sheafCharacterValue (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) T
      (D.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up d)) (ULift.up x) := by
  let : IsCommMonObj D.dual.X := D.commutative
  let : IsCommMonObj E.dual.X := E.commutative
  let x' : T ⟶ E.dual.X := x ≫ (D.bidualEvaluation E).hom.hom
  let χ := E.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up x')
  have hp := SheafBaseChange.Construction.Schemes.representedFppfAbIso_apply (asIso (D.bidualEvaluation E)) T x
  have hp' := congrArg (fun y =>
    SheafEvaluation.Construction.Schemes.sheafCharacterValue (CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) T
      (((CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map D.representedCartierDualIso.inv.op).hom.app (Opposite.op T)
        (E.representedCartierDualIso.hom.hom.app (Opposite.op T) y))
      (D.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up d))) hp
  have hw := SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value D.representedCartierDualIso.inv T χ
    (D.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up d))
  have hc := congrArg (SheafEvaluation.Construction.Schemes.sheafCharacterValue (@CommutativeSheavesAb.Construction.Schemes.representedFppfAb S D.dual D.commutative) T χ)
    (SheafBidual.Construction.Schemes.sheafIso_hom_inv_apply D.representedCartierDualIso T (ULift.up d))
  have he := E.representedCartierDualIso_value T x' d
  have hn := congrArg (fun p : T ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X => ULift.up.{u + 1} p)
    (D.bidualEvaluation_pairing E T x d)
  have hd := D.representedCartierDualIso_value T d x
  exact hp'.trans (hw.trans (hc.trans (he.trans (hn.trans hd.symm))))

/-- The transported native bidual isomorphism is the canonical
evaluation map of the actual commutative fppf sheaf. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.representedBidualIso_hom
    {G : Grp (Over S)} [IsCommMonObj G.X] (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) [IsIso (D.bidualEvaluation E)] :
    (D.representedBidualIso E).hom = SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) := by
  apply SheafEvaluation.Construction.Schemes.sheafDualHom_ext
  intro T x χ
  obtain ⟨x⟩ := x
  obtain ⟨d, rfl⟩ := (D.representedCartierDualSectionsMulEquiv T).surjective χ
  obtain ⟨d⟩ := d
  have he := D.representedBidualIso_pairing E T x d
  have hb := SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_value (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) T (ULift.up x)
    (D.representedCartierDualIso.hom.hom.app (Opposite.op T) (ULift.up d))
  exact he.trans hb.symm

/-- Perfection of the native canonical bidual gives perfection of
canonical bidual evaluation in the full sheaf category. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sheafBidualEvaluation_isIso
    {G : Grp (Over S)} [IsCommMonObj G.X] (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) [IsIso (D.bidualEvaluation E)] :
    IsIso (SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) :=
  D.representedBidualIso_hom E ▸ (D.representedBidualIso E).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
