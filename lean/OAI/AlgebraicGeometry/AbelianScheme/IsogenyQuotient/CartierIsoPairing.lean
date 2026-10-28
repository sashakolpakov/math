import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Pairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PerfectBlocks
import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion

/-! # Cartier Iso Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
An actual isomorphism from the Cartier character representative constructs
a native perfect pairing. Its test-scheme values are the original
characters, evaluated after the inverse isomorphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem Annihilator.Construction.SchemeBicharacter.restrict_isPerfect_of_iso
    {S : Scheme.{u}} {G H U V : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] [IsCommMonObj U.X] [IsCommMonObj V.X]
    (b : Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (hb : b.toSheafPairing.IsPerfect) (i : U ≅ G) (j : V ≅ H) :
    (b.restrict i.hom.hom.hom j.hom.hom.hom).toSheafPairing.IsPerfect := by
  apply b.restrict_isPerfect hb i.hom.hom.hom i.inv.hom.hom
    (congrArg (fun f => f.hom.hom) i.hom_inv_id) j.hom.hom.hom j.inv.hom.hom
    (congrArg (fun f => f.hom.hom) j.hom_inv_id)
  intro T x y
  have hi : i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 G.X := congrArg (fun f => f.hom.hom) i.inv_hom_id
  have hj : j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 H.X := congrArg (fun f => f.hom.hom) j.inv_hom_id
  rw [hi, hj, Category.comp_id, Category.comp_id]

variable {S : Scheme.{u}} {G H : Grp (Over S)} [IsCommMonObj G.X] [IsCommMonObj H.X]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (e : C.dual ≅ H)

def CartierIsoPairing.Construction.inverseCartierIsoSheafPairing : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) := by
  letI : IsCommMonObj C.dual.X := C.commutative
  exact ⟨(CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso e).inv ≫ C.representedCartierDualIso.hom⟩

def CartierIsoPairing.Construction.cartierIsoSchemePairing :
    Annihilator.Construction.SchemeBicharacter (A := G.X) (B := H.X) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  (Sheaf.Pairing.Construction.sheafPairingToScheme (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e)).flip

theorem CartierIsoPairing.Construction.cartierIsoSchemePairing_value (T : Over S) (x : T ⟶ G.X) (y : T ⟶ H.X) :
    (CartierIsoPairing.Construction.cartierIsoSchemePairing C e).pairValue x y = C.evaluationValue T (y ≫ e.inv.hom.hom) x := by
  rw [CartierIsoPairing.Construction.cartierIsoSchemePairing, Annihilator.Construction.SchemeBicharacter.flip_pairValue, Sheaf.Pairing.Construction.sheafPairingToScheme_value]
  rfl

theorem CartierIsoPairing.Construction.inverseCartierIsoSheafPairing_isPerfect
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e).IsPerfect := by
  have : IsCommMonObj C.dual.X := C.commutative
  have hG : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) :=
    ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩
  have hb : IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) :=
    (CartierDuality.PolarizedTorsion.Construction.cartier_duality (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) hG).2.2.1
  have hl : IsIso (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e).leftAdjoint :=
    inferInstanceAs (IsIso ((CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso e).inv ≫ C.representedCartierDualIso.hom))
  let i := @asIso _ _ _ _ (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e).leftAdjoint hl
  let b := @asIso _ _ _ _ (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) hb
  exact ⟨hl, (b ≪≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso i.op).isIso_hom⟩

theorem CartierIsoPairing.Construction.cartierIsoSchemePairing_isPerfect
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom] :
    (CartierIsoPairing.Construction.cartierIsoSchemePairing C e).toSheafPairing.IsPerfect := by
  rw [CartierIsoPairing.Construction.cartierIsoSchemePairing, Annihilator.Construction.SchemeBicharacter.toSheafPairing_flip, Sheaf.Pairing.Construction.sheafPairingToScheme_toSheaf]
  have hp := CartierIsoPairing.Construction.inverseCartierIsoSheafPairing_isPerfect C e
  refine ⟨hp.2, ?_⟩
  have h : (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e).flip.rightAdjoint =
      (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e).leftAdjoint :=
    congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip (CartierIsoPairing.Construction.inverseCartierIsoSheafPairing C e))
  exact h.symm ▸ hp.1

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
