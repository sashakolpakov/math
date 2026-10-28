import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedPoints

/-! # Pairing Nondegeneracy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingNondegeneracy

noncomputable section

/-! Perfectness of the actual sheaf pairing detects points. On a
reduced finite-type geometric fiber, ordinary geometric points suffice
to test the character in the other argument. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplicative.Construction

universe u
section Sheaves
variable {S : Scheme.{u}} {A B : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

theorem schemePairing_nondegenerate_left (he : e.toSheafPairing.IsPerfect)
    (T : Over S) (x : T ⟶ A)
    (hx : ∀ (U : Over S) (f : U ⟶ T) (y : U ⟶ B), e.pairValue (f ≫ x) y = 1) : x = 1 := by
  have : IsIso e.toSheafPairing.leftAdjoint := he.1
  have hi : Function.Injective (e.toSheafPairing.leftAdjoint.hom.app (.op T)) :=
    (ConcreteCategory.bijective_of_isIso (e.toSheafPairing.leftAdjoint.hom.app (.op T))).injective
  have hc : e.sheafCharacterAt T x = e.sheafCharacterAt T 1 := by
    rw [e.sheafCharacterAt_one]
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    rintro ⟨y⟩
    exact congrArg ULift.up (hx U.unop.left U.unop.hom y)
  have hp : ULift.up x = ULift.up (1 : T ⟶ A) := hi hc
  exact congrArg ULift.down hp

end Sheaves

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [LocallyOfFiniteType B.hom] [IsReduced B.left]
  (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))

theorem schemePairing_geometric_nondegenerate_left (he : e.toSheafPairing.IsPerfect)
    (x : Over.mk (𝟙 (Spec (.of k))) ⟶ A)
    (hx : ∀ y : Over.mk (𝟙 (Spec (.of k))) ⟶ B, e.pairValue x y = 1) : x = 1 := by
  let T := Over.mk (𝟙 (Spec (.of k)))
  let p : B ⟶ T := Over.homMk B.hom
  let F := e.pairValue (p ≫ x) (𝟙 B)
  have hF : F = 1 := by
    have : Smooth (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X.hom := IsogenyQuotient.Multiplicative.Construction.multiplicativeGroupOver_smooth _
    have : IsSeparated (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X.hom := IsogenyQuotient.Multiplicative.Construction.multiplicativeGroupOver_separated _
    apply Albanese.Construction.ClosedPoints.hom_ext_of_points B (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X F 1
    intro y
    have hp : y ≫ p = 𝟙 T := Over.OverMorphism.ext y.w
    have hv := e.pairValue_natural y (p ≫ x) (𝟙 B)
    rw [Category.comp_id, ← Category.assoc, hp, Category.id_comp] at hv
    exact hv.symm.trans ((hx y).trans (MonObj.comp_one y).symm)
  apply schemePairing_nondegenerate_left e he T x
  intro U f y
  have hf : y ≫ p = f := by
    apply Over.OverMorphism.ext
    exact y.w.trans (f.w.symm.trans (Category.comp_id f.left))
  have hv := e.pairValue_natural y (p ≫ x) (𝟙 B)
  rw [Category.comp_id, ← Category.assoc, hf] at hv
  exact hv.trans ((congrArg (fun z => y ≫ z) hF).trans (MonObj.comp_one y))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingNondegeneracy
