import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Slice

/-! # Product Lift -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.ProductLift.CrystallinePrincipalProductLift

noncomputable section

/-!
# Native lifts to finite intersections in the principal Čech nerve

The checked preservation of finite limits in the native slice constructs
a morphism to every finite principal intersection from compatible maps
to its factors. Both the morphism and its projection equations live in
the original crystalline slice category.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)
  {α : Type v} [Fintype α] (r : α → PrincipalCoefficient.PrincipalCoefficientCategory.Object Q.thickening.ring)

local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Slice.CrystallinePrincipalSlice.functor p k X Q

def cone (T : Over Q) (f : ∀ i, T ⟶ (U).obj (r i)) : Cone (Discrete.functor r ⋙ U) where
  pt := T
  π :=
    { app i := f i.as
      naturality := by
        intro i j g
        have h : i = j := Discrete.ext (Discrete.eq_of_hom g)
        subst j
        have hg : g = 𝟙 i := Subsingleton.elim _ _
        subst g
        simp }

def lift (T : Over Q) (f : ∀ i, T ⟶ (U).obj (r i)) : T ⟶ (U).obj (∏ᶜ r) :=
  (isLimitOfPreserves U (limit.isLimit (Discrete.functor r))).lift (cone p k X Q r T f)

theorem lift_projection (T : Over Q) (f : ∀ i, T ⟶ (U).obj (r i)) (i : α) :
    CrystallinePrincipalProductLift.lift p k X Q r T f ≫ (U).map (Pi.π r i) = f i :=
  (isLimitOfPreserves U (limit.isLimit (Discrete.functor r))).fac (cone p k X Q r T f) ⟨i⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.ProductLift.CrystallinePrincipalProductLift
