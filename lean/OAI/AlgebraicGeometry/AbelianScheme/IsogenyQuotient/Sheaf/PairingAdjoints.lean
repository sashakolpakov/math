import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PairingRestriction
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms

/-! # Pairing Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
Restriction and adjointness of the original scheme pairing pass to the
same operations in CartierDuality's sheaf category, retaining all test-scheme values.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes

universe u

variable {S : Scheme.{u}} {A B U V : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [GrpObj U] [IsCommMonObj U] [GrpObj V] [IsCommMonObj V]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_projectorsAdjoint
    (p : A ⟶ A) (q : B ⟶ B) [IsMonHom p] [IsMonHom q]
    (h : ∀ (T : Over S) (x : T ⟶ A) (y : T ⟶ B),
      e.pairValue (x ≫ p) y = e.pairValue x (y ≫ q)) :
    CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e.toSheafPairing
      (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk p)) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk q)) := by
  intro T x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  exact (e.toSheafPairing_rightValue T (x ≫ p) y).trans
    ((congrArg ULift.up (h T x y)).trans (e.toSheafPairing_rightValue T x (y ≫ q)).symm)

theorem Annihilator.Construction.SchemeBicharacter.toSheafPairing_restrict (f : U ⟶ A) (g : V ⟶ B) [IsMonHom f] [IsMonHom g] :
    (e.restrict f g).toSheafPairing = e.toSheafPairing.restrict
      (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk f)) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk g)) := by
  have h : (e.restrict f g).toSheafPairing.leftAdjoint =
      (e.toSheafPairing.restrict
        (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk f)) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk g))).leftAdjoint := by
    apply CartierDuality.SheafEvaluation.Construction.Schemes.sheafDualHom_ext
    intro T x y
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have hv := CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (Grp.homMk g)) T
      (e.toSheafPairing.leftAdjoint.hom.app (.op T) (ULift.up (x ≫ f))) (ULift.up y)
    exact ((e.restrict f g).toSheafPairing_value T x y).trans
      ((congrArg ULift.up (e.restrict_pairValue f g x y)).trans
        ((e.toSheafPairing_value T (x ≫ f) (y ≫ g)).symm.trans hv.symm))
  exact congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
