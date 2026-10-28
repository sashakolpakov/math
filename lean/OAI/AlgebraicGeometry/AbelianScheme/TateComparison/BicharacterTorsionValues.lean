import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicTorsionPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues

/-! # Bicharacter Torsion Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BicharacterTorsionValues

noncomputable section

/-! Native finite torsion scheme pairings give biadditive unit values
on the actual finite groups used to define Tate modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

section Additive
variable {A B C X Y Z : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

def biadditiveMap_comp (e : A →+ B →+ C) (f : X →+ A) (g : Y →+ B) (h : C →+ Z) : X →+ Y →+ Z where
  toFun x := h.comp ((e (f x)).comp g)
  map_zero' := by
    ext y
    simp only [AddMonoidHom.comp_apply, map_zero, AddMonoidHom.zero_apply]
  map_add' x z := by
    ext y
    simp only [AddMonoidHom.comp_apply, map_add, AddMonoidHom.add_apply]

end Additive

universe u
variable {S : Scheme.{u}} {A B W : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj W] [IsCommMonObj W]

def schemeBicharacter_biadditive (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (T : Over S) : Additive (T ⟶ A) →+ Additive (T ⟶ B) →+ Additive (T ⟶ W) where
  toFun x := (e.pairRightHom x.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact e.one_left T y.toMul
  map_add' x z := by
    apply AddMonoidHom.ext
    intro y
    exact e.mul_left T x.toMul z.toMul y.toMul

variable {k : Type u} [Field k]
  (A B : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (q : ℕ) [Fact q.Prime] (n : ℕ)

def geometricMultiplicativeUnitHom :
    (Over.mk (𝟙 (Spec (.of k))) ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) →* kˣ :=
  (Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom).comp
    (CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom (Over.mk (𝟙 (Spec (.of k)))))

def finiteTorsionUnitValues
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
      (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X)) :
    Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n →+
      Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) n →+ Additive kˣ :=
  biadditiveMap_comp (schemeBicharacter_biadditive e (Over.mk (𝟙 (Spec (.of k)))))
    (IntrinsicTorsionPoints.nativeTorsionPointEquiv A (Over.mk (𝟙 (Spec (.of k)))) q n).toAddMonoidHom
    (IntrinsicTorsionPoints.nativeTorsionPointEquiv B (Over.mk (𝟙 (Spec (.of k)))) q n).toAddMonoidHom
    (geometricMultiplicativeUnitHom (k := k)).toAdditive

omit [Fact q.Prime] in
theorem finiteTorsionUnitValues_value
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
      (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
    (x : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n)
    (y : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) n) :
    (finiteTorsionUnitValues A B q n e x y).toMul = geometricMultiplicativeUnitHom
      (e.pairValue (IntrinsicTorsionPoints.nativeTorsionPointEquiv A (Over.mk (𝟙 (Spec (.of k)))) q n x).toMul
        (IntrinsicTorsionPoints.nativeTorsionPointEquiv B (Over.mk (𝟙 (Spec (.of k)))) q n y).toMul) := rfl

omit [Fact q.Prime] in
theorem finiteTorsionUnitValues_killed
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
      (A := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A (q ^ n))
      (B := IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B (q ^ n))
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
    (x : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ A)) n)
    (y : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ B)) n) :
    (q ^ n) • finiteTorsionUnitValues A B q n e x y = 0 := by
  have hx : (q ^ n) • x = 0 := Subtype.ext x.property
  have h := congrArg (fun f => f y) ((finiteTorsionUnitValues A B q n e).map_nsmul (q ^ n) x)
  rw [hx, map_zero] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BicharacterTorsionValues
