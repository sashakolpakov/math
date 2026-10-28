import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.UniversalMap

/-! # Category -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory

noncomputable section

/-!
# Crystalline objects with lifted polynomial-frame coordinates

Objects carry actual coordinate lifts in their ambient PD ring, and
morphisms preserve those lifts. The native frame extension gives a
functor into this category, with its fixed total polynomial coordinates.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)

structure Object where
  base : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
  coordinate : σ → base.thickening.ring
  reduction_coordinate : ∀ i, base.thickening.reduction (coordinate i) =
    AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B base (a i)

structure Hom (P Q : Object p k B σ a) where
  hom : P.base ⟶ Q.base
  coordinate_comm : ∀ i, hom.ambientMap (Q.coordinate i) = P.coordinate i

theorem hom_ext {P Q : Object p k B σ a} {f g : FramedCrystallineCategory.Hom p k B σ a P Q} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (Object p k B σ a) where
  Hom := FramedCrystallineCategory.Hom p k B σ a
  id P := ⟨𝟙 P.base, fun _ => rfl⟩
  comp f g :=
    ⟨f.hom ≫ g.hom, fun i => (congrArg f.hom.ambientMap (g.coordinate_comm i)).trans (f.coordinate_comm i)⟩
  id_comp f := hom_ext p k B σ a (Category.id_comp f.hom)
  comp_id f := hom_ext p k B σ a (Category.comp_id f.hom)
  assoc f g h := hom_ext p k B σ a (Category.assoc f.hom g.hom h.hom)

def forget : Object p k B σ a ⥤ Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) where
  obj P := P.base
  map f := f.hom

theorem frame_coordinate_reduction
    (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (i : σ) :
    ((CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a).obj Q).thickening.reduction
      (CrystallineFrame.Map.CrystallineFrameMap.coordinate a Q i) =
    AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B ((CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a).obj Q) (a i) := by
  have hg := CrystallineFrame.Map.CrystallineFrameMap.generator_mem Q 1 one_ne_zero i
  change PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening (Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i) = 0 at hg
  change PolynomialThickening.CrystallinePolynomialThickening.reduction p k Q.residueRing σ Q.thickening
    (algebraMap Q.thickening.ring (DividedPowerAlgebra Q.thickening.ring (σ →₀ Q.thickening.ring))
      (CrystallineFrame.Lifts.CrystallineFrameLifts.lift p k B σ a Q i) + Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.thickening.ring σ 1 i) =
    AffineFrameCover.CrystallineAffineFrameCover.residualMap p k B Q (a i)
  rw [map_add, CrystallineFrame.Map.CrystallineFrameMap.reduction_coefficient, CrystallineFrame.Lifts.CrystallineFrameLifts.reduction_lift, hg, add_zero]

def frameObject (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) : Object p k B σ a where
  base := (CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a).obj Q
  coordinate := CrystallineFrame.Map.CrystallineFrameMap.coordinate a Q
  reduction_coordinate := frame_coordinate_reduction p k B σ a Q

def frame : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) ⥤ Object p k B σ a where
  obj := frameObject p k B σ a
  map f := ⟨(CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a).map f, CrystallineFrame.Map.CrystallineFrameMap.coordinate_naturality a f⟩
  map_id Q := hom_ext p k B σ a ((CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a).map_id Q)
  map_comp f g := hom_ext p k B σ a ((CrystallineFrame.Functor.CrystallineFrameFunctor.functor p k B σ a).map_comp f g)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory
