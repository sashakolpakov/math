import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Decomposition

/-! # Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Pairing.Construction

noncomputable section

/-!
A finite family of scheme bicharacters gives an actual scheme bicharacter
on a group with a natural multiplicative block decomposition. The pairing
map is constructed by evaluation on the two universal points; its formula
on every test scheme is proved from naturality.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

universe u v

variable {S : Scheme.{u}} {T W : Over S} [GrpObj T] [GrpObj W] [IsCommMonObj W]
  {I : Type v} [Fintype I] (G : I → Over S) [∀ i, GrpObj (G i)]
  (D : ∀ X : Over S, (X ⟶ T) ≃* (∀ i, X ⟶ G i))
  (hD : ∀ {X Y : Over S} (f : X ⟶ Y) (x : Y ⟶ T) (i : I),
    D X (f ≫ x) i = f ≫ D Y x i)
  (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := G i) (B := G i) (W := W))

def productPairValue {X : Over S} (x y : X ⟶ T) : X ⟶ W :=
  ∏ i, (e i).pairValue (D X x i) (D X y i)

include hD in
theorem productPairValue_natural {X Y : Over S} (f : X ⟶ Y) (x y : Y ⟶ T) :
    productPairValue G D e (f ≫ x) (f ≫ y) = f ≫ productPairValue G D e x y := by
  unfold productPairValue
  simp_rw [hD, Annihilator.Construction.SchemeBicharacter.pairValue_natural]
  let c : (Y ⟶ W) →* (X ⟶ W) :=
    ⟨⟨fun z => f ≫ z, MonObj.comp_one f⟩, MonObj.comp_mul f⟩
  exact (map_prod c _ _).symm

def productSchemeBicharacter : Annihilator.Construction.SchemeBicharacter (A := T) (B := T) (W := W) where
  hom := productPairValue G D e (fst T T) (snd T T)
  one_left X y := by
    rw [← productPairValue_natural G D hD e, lift_fst, lift_snd]
    simp only [productPairValue, map_one, Pi.one_apply]
    simp_rw [Annihilator.Construction.SchemeBicharacter.pairValue, Annihilator.Construction.SchemeBicharacter.one_left]
    exact Finset.prod_const_one
  one_right X x := by
    rw [← productPairValue_natural G D hD e, lift_fst, lift_snd]
    simp only [productPairValue, map_one, Pi.one_apply]
    simp_rw [Annihilator.Construction.SchemeBicharacter.pairValue, Annihilator.Construction.SchemeBicharacter.one_right]
    exact Finset.prod_const_one
  mul_left X x z y := by
    simp only [← productPairValue_natural G D hD e, lift_fst, lift_snd]
    simp only [productPairValue, map_mul, Pi.mul_apply]
    simp_rw [Annihilator.Construction.SchemeBicharacter.pairValue, Annihilator.Construction.SchemeBicharacter.mul_left]
    exact Finset.prod_mul_distrib
  mul_right X x y z := by
    simp only [← productPairValue_natural G D hD e, lift_fst, lift_snd]
    simp only [productPairValue, map_mul, Pi.mul_apply]
    simp_rw [Annihilator.Construction.SchemeBicharacter.pairValue, Annihilator.Construction.SchemeBicharacter.mul_right]
    exact Finset.prod_mul_distrib

theorem productSchemeBicharacter_pairValue {X : Over S} (x y : X ⟶ T) :
    (productSchemeBicharacter G D hD e).pairValue x y =
      ∏ i, (e i).pairValue (D X x i) (D X y i) := by
  change lift x y ≫ productPairValue G D e (fst T T) (snd T T) = _
  rw [← productPairValue_natural G D hD e, lift_fst, lift_snd]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Pairing.Construction
