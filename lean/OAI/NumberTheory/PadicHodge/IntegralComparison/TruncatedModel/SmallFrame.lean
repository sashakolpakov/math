import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CrystallineDiagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow

/-! # Small Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame

noncomputable section

/-! Affine frames of the actual finite-level smooth model are open
crystalline thickenings in both original small-site presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of k))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

def bigFunctor := FrameFunctor.functor p k n X Y f hp ⋙
  BoundedCrystalline.Site.inclusion (Witt.Crystalline.wittStructureMap p k Y) n

theorem mapToX_open (U : X.left.affineOpens) :
    IsOpenImmersion ((bigFunctor p k n X Y f hp).obj U).mapToX := by
  let e := Truncated.SmoothFrame.quotientEquiv p
    (Truncated.AffineModelFrame.sourceRing p k n X U.val)
    (Truncated.AffineModelFrame.targetRing p k n X Y f U.val)
    (Truncated.AffineModelFrame.reduction p k n X Y f U.val)
    (Truncated.AffineModelFrame.reduction_surjective p k n X Y f hp U.val U.property)
    (Truncated.AffineModelFrame.reduction_kernel p k n X Y f hp U.val U.property)
  change IsOpenImmersion ((Scheme.Spec.mapIso e.toCommRingCatIso.symm.op).hom ≫
    Truncated.AffineModelFrame.chart p k n X Y f hp U.val U.property)
  infer_instance

def smallFunctor : X.left.affineOpens ⥤ Witt.Crystalline.CrystallineObject p k Y :=
  Open.CrystallineDiagram.functor (bigFunctor p k n X Y f hp) (mapToX_open p k n X Y f hp)

def functor : X.left.affineOpens ⥤ AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k Y :=
  smallFunctor p k n X Y f hp ⋙ GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to62

theorem map_ambient {U V : X.left.affineOpens} (a : U ⟶ V) (x : Γ(X.left, V.val)) :
    ((functor p k n X Y f hp).map a).ambientMap x =
      (X.left.presheaf.map (homOfLE (leOfHom a)).op).hom x :=
  FrameFunctor.map_apply p k n X Y f hp U.val V.val U.property V.property
    (leOfHom a) x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmallFrame
