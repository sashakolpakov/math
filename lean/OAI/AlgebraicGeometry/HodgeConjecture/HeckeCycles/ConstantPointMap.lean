import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

/-! # Constant Point Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointMap.CM

noncomputable section

/-! Actual maps from a constant scheme into a scheme over the same
base are determined by their base-valued points. This supplies the
geometric map associated with the constructed torsion coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

universe u
variable (S : Scheme.{u}) (I : Type u) (A : Over S)

def point (i : I) : Over.mk (𝟙 S) ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I :=
  Over.homMk (Sigma.ι (fun _ : I => S) i) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)

def ofPoints (p : I → (Over.mk (𝟙 S) ⟶ A)) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ⟶ A :=
  Over.homMk (Sigma.desc (fun i => (p i).left)) (by
    apply Sigma.hom_ext
    intro i
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z : S ⟶ A.left => z ≫ A.hom) (Sigma.ι_comp_desc _ _)).trans
        (p i).w)).trans (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i).symm)

@[reassoc]
theorem point_ofPoints (p : I → (Over.mk (𝟙 S) ⟶ A)) (i : I) :
    point S I i ≫ ofPoints S I A p = p i := by
  apply Over.OverMorphism.ext
  exact Sigma.ι_comp_desc _ _

theorem hom_ext (f g : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ⟶ A)
    (h : ∀ i, point S I i ≫ f = point S I i ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  exact congrArg (fun z : Over.mk (𝟙 S) ⟶ A => z.left) (h i)

theorem ofPoints_on_constant (p : I → (Over.mk (𝟙 S) ⟶ A))
    (T : Over S) (x : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I) (i : I)
    (hx : ∀ t, AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T x t = i) :
    x ≫ ofPoints S I A p = Over.homMk T.hom (Category.comp_id T.hom) ≫ p i := by
  apply Over.OverMorphism.ext
  change x.left ≫ (ofPoints S I A p).left = T.hom ≫ (p i).left
  calc
    x.left ≫ (ofPoints S I A p).left =
        ((x.left ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom) ≫ Sigma.ι (fun _ : I => S) i) ≫
          (ofPoints S I A p).left :=
      congrArg (fun z => z ≫ (ofPoints S I A p).left) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_factor x.left i hx)
    _ = T.hom ≫ (Sigma.ι (fun _ : I => S) i ≫ (ofPoints S I A p).left) := by
      rw [x.w]
      exact Category.assoc _ _ _
    _ = T.hom ≫ (p i).left :=
      congrArg (fun z => T.hom ≫ z)
        (congrArg (fun z : Over.mk (𝟙 S) ⟶ A => z.left) (point_ofPoints S I A p i))

def mapsEquiv : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I ⟶ A) ≃ (I → (Over.mk (𝟙 S) ⟶ A)) where
  toFun f i := point S I i ≫ f
  invFun := ofPoints S I A
  left_inv f := CM.hom_ext S I A _ _ (point_ofPoints S I A (fun i => point S I i ≫ f))
  right_inv p := funext (point_ofPoints S I A p)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ConstantPointMap.CM
