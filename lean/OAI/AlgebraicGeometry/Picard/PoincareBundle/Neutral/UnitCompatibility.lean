import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.TotalTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberSectionGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionDescentCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport

/-! # Unit Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.UnitCompatibility

noncomputable section

/-!
# The genuine neutral unit frame has its full geometric quotient descent equation
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.ParameterScheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hcomm : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))

/-- Restrict the original genuine quotient datum to its actual neutral-axis square. -/
def overDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => g) :=
  Recovered.OverSquare.pulledDatum (f ⊗ₘ g) g (ParameterScheme.point A X) (ParameterScheme.point B Y) (ParameterScheme.point_naturality f g).symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm)

/-- Its full underlying geometric datum on the neutral-axis cover. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => g.left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => g)
    (overDatum f g L Dh Dv Kh Kv hcomm)

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi ht in
/-- The actual normalized unit section respects the native pulled descent gluing on every test scheme. -/
theorem normalized_gluing {T : Over S} (base : T ⟶ Y) (p q : T ⟶ X)
    (hp : p ≫ g = base) (hq : q ≫ g = base) :
    Bilinear.ContractionPullback.pulledSection p.left (ParameterScheme.unitFrame A X L Dh).hom ≫
      (overDatum f g L Dh Dv Kh Kv hcomm).hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
    Bilinear.ContractionPullback.pulledSection q.left (ParameterScheme.unitFrame A X L Dh).hom := by
  have ha : (p ≫ ParameterScheme.point A X) ≫ fst A X = 1 := by rw [Category.assoc, ParameterScheme.point_neutral, MonObj.comp_one]
  have hb : (q ≫ ParameterScheme.point A X) ≫ fst A X = 1 := by rw [Category.assoc, ParameterScheme.point_neutral, MonObj.comp_one]
  have himage : (p ≫ ParameterScheme.point A X) ≫ (f ⊗ₘ g) = (q ≫ ParameterScheme.point A X) ≫ (f ⊗ₘ g) :=
    Product.TransportGluing.square_images _ _ _ _ (ParameterScheme.point_naturality f g) p q (hp.trans hq.symm)
  let σ : Line.Fibers.fiber L (p ≫ ParameterScheme.point A X) ⟶ Line.Fibers.fiber L (q ≫ ParameterScheme.point A X) :=
    RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
    (p ≫ ParameterScheme.point A X) (q ≫ ParameterScheme.point A X) himage
  have hs : Line.Fibers.pullSection L p (ParameterScheme.point A X) (p ≫ ParameterScheme.point A X) rfl (ParameterScheme.unitFrame A X L Dh).hom ≫ σ =
      Line.Fibers.pullSection L q (ParameterScheme.point A X) (q ≫ ParameterScheme.point A X) rfl (ParameterScheme.unitFrame A X L Dh).hom := by
    exact (congrArg (fun a => a ≫ σ)
      (Dh.unit_natural p (ParameterScheme.point A X) (p ≫ ParameterScheme.point A X) (ParameterScheme.point_neutral A X) ha rfl)).trans
      ((TotalTransport.total_unit_neutral f g L Dh Dv Kh Kv hi ht _ _ ha hb himage).trans
        (Dh.unit_natural q (ParameterScheme.point A X) (q ≫ ParameterScheme.point A X) (ParameterScheme.point_neutral A X) hb rfl).symm)
  have hg : (overDatum f g L Dh Dv Kh Kv hcomm).hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
      FiberBilinearGluing.fiberTransport L p q (ParameterScheme.point A X) σ := by
    exact (Recovered.OverSquare.pulledHom (f ⊗ₘ g) g (ParameterScheme.point A X) (ParameterScheme.point B Y) (ParameterScheme.point_naturality f g).symm
      (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) base p q hp hq).trans
      (FiberBilinearGluing.fiberTransport_eq_comp L p q (ParameterScheme.point A X) σ).symm
  rw [hg]
  exact FiberSectionGluing.section_gluing L p q (ParameterScheme.point A X) (ParameterScheme.unitFrame A X L Dh).hom σ hs

include hi ht in
/-- On the actual scheme kernel pair, the normalized original unit is invariant under the full geometric gluing. -/
theorem kernelPair_gluing :
    Bilinear.ContractionPullback.pulledSection (pullback.fst g.left g.left) (ParameterScheme.unitFrame A X L Dh).hom ≫
      (Geometric.CechInvariant.relationGluing g.left (ordinaryDatum f g L Dh Dv Kh Kv hcomm)).hom =
    Bilinear.ContractionPullback.pulledSection (pullback.snd g.left g.left) (ParameterScheme.unitFrame A X L Dh).hom :=
  normalized_gluing f g L Dh Dv Kh Kv hcomm hi ht (UnderlyingDescent.baseMap (Product.SquareTransport.testBase g))
    (Product.SquareTransport.firstPoint g) (Product.SquareTransport.secondPoint g)
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => g) (i := PUnit.unit) (Product.SquareTransport.testBase g)
      (pullback.fst g.left g.left) pullback.condition)
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => g) (i := PUnit.unit) (Product.SquareTransport.testBase g)
      (pullback.snd g.left g.left) rfl)

/-- The actual source-cover map obtained from the original normalized unit frame. -/
def coverUnit : (Scheme.Modules.pullback g.left).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y.left) ⟶ Line.Fibers.fiber L (ParameterScheme.point A X) :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g.left).hom ≫ (ParameterScheme.unitFrame A X L Dh).hom

include hi ht in
/-- The genuine original unit supplies a compatible morphism from the quotient structure sheaf. -/
theorem coverUnit_compatible :
    (Scheme.Modules.pullback (pullback.fst g.left g.left)).map (coverUnit g L Dh) ≫
      (Geometric.CechInvariant.relationGluing g.left (ordinaryDatum f g L Dh Dv Kh Kv hcomm)).hom =
    (Cech.MateNormalization.standardGluing g.left (pullback.fst g.left g.left) (pullback.snd g.left g.left) pullback.condition).hom.app
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y.left) ≫ (Scheme.Modules.pullback (pullback.snd g.left g.left)).map (coverUnit g L Dh) :=
  SectionDescentCompatibility.compatible g.left (pullback.fst g.left g.left) (pullback.snd g.left g.left)
    pullback.condition (ParameterScheme.unitFrame A X L Dh).hom _ (kernelPair_gluing f g L Dh Dv Kh Kv hcomm hi ht)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.UnitCompatibility
