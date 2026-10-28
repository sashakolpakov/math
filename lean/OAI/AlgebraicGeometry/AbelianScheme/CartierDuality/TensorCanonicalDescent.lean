import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorFrames

/-! # Tensor Canonical Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorCanonicalDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: canonical tensor comparison preserves actual line gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.SheafMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.UnitPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

universe u

/-- Inverting a comparison square commutes with tensoring its two input isomorphisms. -/
theorem tensorSquare_inverse {T : Scheme.{u}} {L L' M M' W W' : T.Modules}
    (l : L ≅ L') (m : M ≅ M') (w : W ≅ W')
    (p : W' ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L' M') (a : W ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M)
    (h : p ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap l.inv m.inv = w.inv ≫ a) :
    a ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap l.hom m.hom = w.hom ≫ p := by
  apply (cancel_epi w.inv).mp
  rw [← Category.assoc, ← h, Category.assoc, Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_comp,
    l.inv_hom_id, m.inv_hom_id, Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_id, Category.comp_id,
    ← Category.assoc, w.inv_hom_id, Category.id_comp]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules)

/-- The tensor comparison respects the canonical comparison with a common composite map. -/
theorem tensorComparison_composite {T : Scheme.{u}} (q : T ⟶ Y) (x : T ⟶ X) (hx : x ≫ f = q) :
    (Scheme.Modules.pullback x).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L M) ≫
      Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap x ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M) ≫
        Picard.PoincareBundle.Tensor.SheafMaps.tensorMap ((Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app L)
          ((Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app M) =
    (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) ≫
      Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap q L M := by
  cases hx
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  exact tensorSquare_inverse ((Scheme.Modules.pullbackComp x f).app L)
    ((Scheme.Modules.pullbackComp x f).app M) ((Scheme.Modules.pullbackComp x f).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M))
    (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap (x ≫ f) L M)
    ((Scheme.Modules.pullback x).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L M) ≫
      Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap x ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M))
    (Picard.PoincareBundle.Tensor.PullbackComposition.pullbackMap_comp_inv x f L M)

/-- Two tensor comparison squares give the comparison of their induced gluing maps. -/
theorem tensorSquare_gluing {T : Scheme.{u}} {L L' L'' M M' M'' W W' W'' : T.Modules}
    (lx : L ≅ L'') (ly : L' ≅ L'') (mx : M ≅ M'') (my : M' ≅ M'')
    (wx : W ≅ W'') (wy : W' ≅ W'') (a : W ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M) (b : W' ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L' M')
    (p : W'' ⟶ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L'' M'')
    (hx : a ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap lx.hom mx.hom = wx.hom ≫ p)
    (hy : b ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap ly.hom my.hom = wy.hom ≫ p) :
    a ≫ Picard.PoincareBundle.Tensor.SheafMaps.tensorMap (lx.hom ≫ ly.inv) (mx.hom ≫ my.inv) = (wx.hom ≫ wy.inv) ≫ b := by
  apply (cancel_mono (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap ly.hom my.hom)).mp
  rw [Category.assoc, Picard.PoincareBundle.Tensor.SheafMaps.tensorMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hx, hy, Iso.inv_hom_id_assoc]

/-- The canonical tensor pullback maps intertwine the complete native descent gluing. -/
theorem tensorComparison_gluing {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    ((Scheme.Modules.pullback x).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L M) ≫
      Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap x ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M)) ≫
        Picard.PoincareBundle.Tensor.SheafMaps.tensorMap ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L).hom q x y hx hy)
          ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M).hom q x y hx hy) =
    (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M)).hom q x y hx hy ≫
      ((Scheme.Modules.pullback y).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L M) ≫
        Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap y ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj M)) := by
  rw [Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom, Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom, Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom]
  exact tensorSquare_gluing
    ((Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).app L)
    ((Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy).app L)
    ((Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).app M)
    ((Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy).app M)
    ((Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M))
    ((Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy).app (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule L M))
    _ _ (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap q L M) (tensorComparison_composite f L M q x hx)
      (tensorComparison_composite f L M q y hy)

variable (L' M' : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

/-- The actual tensor frame on the cover. -/
def tensorCoverFrame
    (e : (Scheme.Modules.pullback f).obj L'.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : (Scheme.Modules.pullback f).obj M'.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    (Scheme.Modules.pullback f).obj (L'.tensor M').sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  Picard.PoincareBundle.Tensor.LinePullback.pullbackIso f L'.sheaf M'.sheaf L'.locallyTrivial M'.locallyTrivial ≪≫
    TensorFrames.Construction.LineDescent.tensorFrame e d

/-- The successive actual tensor comparison on each test scheme. -/
def tensorCoverComparison {T : Scheme.{u}} (x : T ⟶ X) :
    (Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback f).obj (L'.tensor M').sheaf) ≅
      AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback f).obj L'.sheaf))
        ((Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback f).obj M'.sheaf)) :=
  (Scheme.Modules.pullback x).mapIso
    (Picard.PoincareBundle.Tensor.LinePullback.pullbackIso f L'.sheaf M'.sheaf L'.locallyTrivial M'.locallyTrivial) ≪≫
      Picard.PoincareBundle.Tensor.LinePullback.pullbackIso x _ _
        (L'.pullback f).locallyTrivial (M'.pullback f).locallyTrivial

/-- The tensor frame and the two separate pulled frames agree through the canonical comparison. -/
theorem tensorCoverFrame_pullback
    (e : (Scheme.Modules.pullback f).obj L'.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : (Scheme.Modules.pullback f).obj M'.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {T : Scheme.{u}} (x : T ⟶ X) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (tensorCoverFrame f L' M' e d) x =
      tensorCoverComparison f L' M' x ≪≫ TensorFrames.Construction.LineDescent.tensorFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x) := by
  apply Iso.ext
  change (Scheme.Modules.pullback x).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L'.sheaf M'.sheaf ≫ (TensorFrames.Construction.LineDescent.tensorFrame e d).hom) ≫
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom =
    ((Scheme.Modules.pullback x).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L'.sheaf M'.sheaf) ≫
      Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap x ((Scheme.Modules.pullback f).obj L'.sheaf) ((Scheme.Modules.pullback f).obj M'.sheaf)) ≫ _
  rw [Functor.map_comp, Category.assoc]
  exact congrArg (fun a => (Scheme.Modules.pullback x).map (Picard.PoincareBundle.Tensor.PullbackMap.pullbackMap f L'.sheaf M'.sheaf) ≫ a)
    (TensorFrames.Construction.LineDescent.tensorFrame_pullback x e d)

/-- Tensoring two trivialized lines multiplies their full native descent scalars. -/
theorem tensorCanonicalDescent_scalar
    (e : (Scheme.Modules.pullback f).obj L'.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : (Scheme.Modules.pullback f).obj M'.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (L'.tensor M').sheaf)
      (tensorCoverFrame f L' M' e d) q x y hx hy =
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L'.sheaf) e q x y hx hy *
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M'.sheaf) d q x y hx hy := by
  have ht := tensorComparison_gluing f L'.sheaf M'.sheaf q x y hx hy
  have he := FramedRecovery.Construction.LineDescent.conjugate_intertwiner (tensorCoverComparison f L' M' x) (tensorCoverComparison f L' M' y)
    (TensorFrames.Construction.LineDescent.tensorFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x))
    (TensorFrames.Construction.LineDescent.tensorFrame (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d y))
    ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (L'.tensor M').sheaf).hom q x y hx hy)
    (Picard.PoincareBundle.Tensor.SheafMaps.tensorMap ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L'.sheaf).hom q x y hx hy)
      ((Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M'.sheaf).hom q x y hx hy)) ht
  have hframe := congrArg₂
    (fun (a : (Scheme.Modules.pullback x).obj ((Scheme.Modules.pullback f).obj (L'.tensor M').sheaf) ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T)
      (b : (Scheme.Modules.pullback y).obj ((Scheme.Modules.pullback f).obj (L'.tensor M').sheaf) ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) =>
      a.inv ≫ (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (L'.tensor M').sheaf).hom q x y hx hy ≫ b.hom)
    (tensorCoverFrame_pullback f L' M' e d x) (tensorCoverFrame_pullback f L' M' e d y)
  exact (congrArg (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue T) (hframe.trans he)).trans
    (TensorFrames.Construction.LineDescent.tensorFrame_scalar (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame e y)
      (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d x) (Picard.Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame d y) _ _)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TensorCanonicalDescent.Construction.LineDescent
