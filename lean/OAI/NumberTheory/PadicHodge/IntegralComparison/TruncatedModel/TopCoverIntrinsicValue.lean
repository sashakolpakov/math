import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.AdditiveTopGlobal

/-! # Top Cover Intrinsic Value -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverIntrinsicValue.Intrinsic

noncomputable section

/-! The original top-form class on the native small cover has the
signed original crystalline comparison as its actual global value. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

private theorem map_unit {A B : AddCommGrpCat.{u}} (a : A ⟶ B) (s : ℤˣ) (x : A) :
    a (s • x) = s • a x := by
  change a ((s : ℤ) • x) = (s : ℤ) • a x
  exact map_zsmul a.hom _ _

private theorem literal_value {A B C : AddCommGrpCat.{u}} (d : A ≅ B)
    {w : A ⟶ C} {v : B ⟶ C} (h : v = d.inv ≫ w)
    {s : ℤˣ} {z : B} {y : C} (hy : y = s • v z) :
    y = s • w (d.inv z) :=
  hy.trans (congrArg (fun a => s • a) (ConcreteCategory.congr_hom h z))

private theorem recover_value {A B C D E : AddCommGrpCat.{u}}
    (e : A ≅ B) (d : C ≅ D) (a : B ⟶ C) (v : A ⟶ E) (w : C ⟶ E) [IsIso w]
    (x : A) (b : B) (z : D) (s : ℤˣ)
    (hc : e.hom ≫ a = v ≫ inv w) (hx : e.hom x = b)
    (hv : v x = s • w (d.inv z)) : a b = s • d.inv z := by
  have h := ConcreteCategory.congr_hom hc x
  change a (e.hom x) = inv w (v x) at h
  calc
    a b = inv w (v x) := (congrArg a hx).symm.trans h
    _ = inv w (s • w (d.inv z)) := congrArg (inv w) hv
    _ = s • inv w (w (d.inv z)) := map_unit (inv w) s _
    _ = s • d.inv z := congrArg (fun y => s • y)
      (ConcreteCategory.congr_hom (IsIso.hom_inv_id w) (d.inv z))

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))
  (g : ℕ) [SmoothOfRelativeDimension g X.hom]

abbrev cover := AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X

theorem comparison (x : IntrinsicDeRham.TopEdge.Intrinsic.source (Truncated.Witt.Ring p k n) X
    (cover p k n X) g) :
    TopCover.globalMap p k n X Y f hp I g (cover p k n X)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X)
      (ModelAdditiveTop.coefficientMorphism p k n X g
        (ULift.up.{2,1} (ULift.up.{1,0} x))) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) g g •
      (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g)).inv
        (IntrinsicCohomology.Intrinsic.comparisonEquiv p k n X Y f hp I (g+g)
          (IntrinsicDeRham.TopEdge.Intrinsic.map (Truncated.Witt.Ring p k n) X (cover p k n X) g x)) := by
  let := AdditiveGlobal.ResolutionFlasque.additive_edge_isIso p k n X Y f I
    (cover p k n X) (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X) (g+g)
  apply recover_value
    (TopCover.originalIso p k n X g (cover p k n X))
    (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g))
    (TopCover.globalMap p k n X Y f hp I g (cover p k n X)
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X))
    (homologyMap (AdditiveTopGlobal.map p k n X Y f hp I g) (g+g))
    (homologyMap (Presheaf.OrderedCechEdge.edge (cover p k n X)
      (AdditiveGlobal.target p k n X Y f I)) (g+g))
    (ModelAdditiveTop.input p k n X g x)
  · exact TopCover.original_coordinates p k n X Y f hp I g
      (cover p k n X) (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.cover (Truncated.Witt.Ring p k n) X)
  · exact ModelAdditiveTop.input_coordinates p k n X g x
  · exact literal_value
      (AdditiveGlobal.globalHomologyIso p k n X Y f I (g+g))
      (AdditiveGlobal.literal p k n X Y f I (cover p k n X) (g+g))
      (AdditiveTopGlobal.comparison p k n X Y f hp I g x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.TopCoverIntrinsicValue.Intrinsic
