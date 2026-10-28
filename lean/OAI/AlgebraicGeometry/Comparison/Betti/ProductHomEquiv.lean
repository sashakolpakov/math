import Mathlib

/-! # Product Hom Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProductHomEquiv.Disjoint

noncomputable section

/-! The linear universal property of products and normalization of adjoint images. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  {ι : Type*} (A : C) (B : ι → C) [HasProduct B]

def homProductLinearEquiv : (A ⟶ ∏ᶜ B) ≃ₗ[R] (∀ i, A ⟶ B i) where
  toFun a i := a ≫ Pi.π B i
  invFun a := Pi.lift a
  left_inv a := by
    apply Pi.hom_ext
    intro i
    exact Pi.lift_comp_π _ i
  right_inv a := funext fun i => Pi.lift_comp_π a i
  map_add' a b := by
    funext i
    change (a + b) ≫ Pi.π B i = a ≫ Pi.π B i + b ≫ Pi.π B i
    simp only [Preadditive.add_comp]
  map_smul' c a := by
    funext i
    change (c • a) ≫ Pi.π B i = c • (a ≫ Pi.π B i)
    simp only [Linear.smul_comp]

theorem homProductLinearEquiv_apply (a : A ⟶ ∏ᶜ B) (i : ι) :
    homProductLinearEquiv (R := R) A B a i = a ≫ Pi.π B i := rfl

variable {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

omit [Preadditive C] in
theorem homEquiv_map {X Y : C} (a : X ⟶ Y) :
    adj.homEquiv X (F.obj Y) (F.map a) = a ≫ adj.unit.app Y := by
  simpa only [Category.comp_id, adj.homEquiv_id] using
    adj.homEquiv_naturality_left a (𝟙 (F.obj Y))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProductHomEquiv.Disjoint
