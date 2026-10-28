import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy

/-! # Pairing Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-!
Restrict an actual source scheme pairing along actual group homomorphisms.
Alternation implies the skew relation needed to recover the opposite
blocks in the full split formula.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A B U V W : Over S}
  [GrpObj A] [GrpObj B] [GrpObj U] [GrpObj V] [GrpObj W]

def Annihilator.Construction.SchemeBicharacter.restrict (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (f : U ⟶ A) (g : V ⟶ B) [IsMonHom f] [IsMonHom g] :
    Annihilator.Construction.SchemeBicharacter (A := U) (B := V) (W := W) where
  hom := (f ⊗ₘ g) ≫ e.hom
  one_left X y := by
    rw [← Category.assoc, lift_map, MonObj.one_comp]
    exact e.one_left X _
  one_right X x := by
    rw [← Category.assoc, lift_map, MonObj.one_comp]
    exact e.one_right X _
  mul_left X x z y := by
    simp only [← Category.assoc, lift_map, MonObj.mul_comp]
    exact e.mul_left X _ _ _
  mul_right X x y z := by
    simp only [← Category.assoc, lift_map, MonObj.mul_comp]
    exact e.mul_right X _ _ _

theorem Annihilator.Construction.SchemeBicharacter.restrict_pairValue (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := W))
    (f : U ⟶ A) (g : V ⟶ B) [IsMonHom f] [IsMonHom g]
    {X : Over S} (x : X ⟶ U) (y : X ⟶ V) :
    (e.restrict f g).pairValue x y = e.pairValue (x ≫ f) (y ≫ g) := by
  simp only [Annihilator.Construction.SchemeBicharacter.pairValue, Annihilator.Construction.SchemeBicharacter.restrict, ← Category.assoc, lift_map]

omit [GrpObj B] [GrpObj U] [GrpObj V] in
theorem Annihilator.Construction.SchemeBicharacter.skew_of_alternating (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := W))
    (halt : ∀ (X : Over S) (x : X ⟶ A), e.pairValue x x = 1)
    (X : Over S) (x y : X ⟶ A) : e.pairValue y x = (e.pairValue x y)⁻¹ := by
  have h := halt X (x * y)
  change e.pairLeftHom (x * y) (x * y) = 1 at h
  rw [map_mul] at h
  change e.pairRightHom x (x * y) * e.pairRightHom y (x * y) = 1 at h
  rw [map_mul, map_mul] at h
  change (e.pairValue x x * e.pairValue x y) * (e.pairValue y x * e.pairValue y y) = 1 at h
  rw [halt X x, halt X y, one_mul, mul_one] at h
  exact eq_inv_of_mul_eq_one_right h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
