import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff

/-! # Locally Constant Fiber Map -/

namespace OAI.RepresentationTheory.Theta.Geometric.LocallyConstantFiberMap

noncomputable section

/-! Open label fibers are preserved by arbitrary maps with matching
locally constant labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def locallyConstantFiberLift {T V : Scheme.{u}} {I : Type u} (r : V ⟶ T)
    (c : LocallyConstant T I) (a : I) (h : ∀ v, c (r v) = a) :
    V ⟶ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).toScheme :=
  IsOpenImmersion.lift (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι r (by
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨r v, h v⟩, rfl⟩)

theorem locallyConstantFiberLift_fac {T V : Scheme.{u}} {I : Type u} (r : V ⟶ T)
    (c : LocallyConstant T I) (a : I) (h : ∀ v, c (r v) = a) :
    locallyConstantFiberLift r c a h ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι = r :=
  IsOpenImmersion.lift_fac _ _ _

theorem translated_relation_of_factor {X T V : Scheme.{u}} (t : X ⟶ X) (x y : T ⟶ X)
    (U : T.Opens) (h : U.ι ≫ y = (U.ι ≫ x) ≫ t)
    (r : V ⟶ T) (s : V ⟶ U.toScheme) (hs : s ≫ U.ι = r) : r ≫ y = (r ≫ x) ≫ t := by
  rw [← hs, Category.assoc, h]
  simp only [Category.assoc]

def locallyConstantFiberMap {T U : Scheme.{u}} {I : Type u} (r : U ⟶ T)
    (c : LocallyConstant T I) (d : LocallyConstant U I) (hd : ∀ x, d x = c (r x)) (a : I) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).toScheme ⟶ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).toScheme :=
  IsOpenImmersion.lift (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι ≫ r) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨r x.val, (hd x.val).symm.trans x.property⟩, rfl⟩)

theorem locallyConstantFiberMap_fac {T U : Scheme.{u}} {I : Type u} (r : U ⟶ T)
    (c : LocallyConstant T I) (d : LocallyConstant U I) (hd : ∀ x, d x = c (r x)) (a : I) :
    locallyConstantFiberMap r c d hd a ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber c a).ι =
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber d a).ι ≫ r := IsOpenImmersion.lift_fac _ _ _

end

end OAI.RepresentationTheory.Theta.Geometric.LocallyConstantFiberMap
