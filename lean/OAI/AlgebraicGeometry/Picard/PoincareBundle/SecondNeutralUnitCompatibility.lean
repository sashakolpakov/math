import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralTotalTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberSectionGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionDescentCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport

/-! # Second Neutral Unit Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralUnitCompatibility

noncomputable section

/-!
# The genuine second neutral unit frame has its full geometric quotient descent equation
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hcomm : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))

/-- Restrict the original genuine quotient datum to its actual second neutral-axis square. -/
def overDatum : (Geometric.KernelLinearization.overModulePullbacks S).DescentData (fun (_ : PUnit.{1}) => f) :=
  Recovered.OverSquare.pulledDatum (f ⊗ₘ g) f (SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.point B Y) (SecondNeutralParameterScheme.point_naturality f g).symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm)

/-- Its full underlying geometric datum on the second neutral-axis cover. -/
def ordinaryDatum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f.left) :=
  UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks (fun (_ : PUnit.{1}) => f)
    (overDatum f g L Dh Dv Kh Kv hcomm)

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi ht in
/-- The actual normalized unit section respects the native pulled descent gluing on every test scheme. -/
theorem normalized_gluing {T : Over S} (base : T ⟶ B) (p q : T ⟶ A)
    (hp : p ≫ f = base) (hq : q ≫ f = base) :
    Bilinear.ContractionPullback.pulledSection p.left (SecondNeutralParameterScheme.unitFrame A X L Dv).hom ≫
      (overDatum f g L Dh Dv Kh Kv hcomm).hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
    Bilinear.ContractionPullback.pulledSection q.left (SecondNeutralParameterScheme.unitFrame A X L Dv).hom := by
  have ha : (p ≫ SecondNeutralParameterScheme.point A X) ≫ snd A X = 1 := by rw [Category.assoc, SecondNeutralParameterScheme.point_neutral, MonObj.comp_one]
  have hb : (q ≫ SecondNeutralParameterScheme.point A X) ≫ snd A X = 1 := by rw [Category.assoc, SecondNeutralParameterScheme.point_neutral, MonObj.comp_one]
  have himage : (p ≫ SecondNeutralParameterScheme.point A X) ≫ (f ⊗ₘ g) = (q ≫ SecondNeutralParameterScheme.point A X) ≫ (f ⊗ₘ g) :=
    Product.TransportGluing.square_images _ _ _ _ (SecondNeutralParameterScheme.point_naturality f g) p q (hp.trans hq.symm)
  let σ : Line.Fibers.fiber L (p ≫ SecondNeutralParameterScheme.point A X) ⟶ Line.Fibers.fiber L (q ≫ SecondNeutralParameterScheme.point A X) :=
    RectangularTransport.total f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv)
    (p ≫ SecondNeutralParameterScheme.point A X) (q ≫ SecondNeutralParameterScheme.point A X) himage
  have hs : Line.Fibers.pullSection L p (SecondNeutralParameterScheme.point A X) (p ≫ SecondNeutralParameterScheme.point A X) rfl (SecondNeutralParameterScheme.unitFrame A X L Dv).hom ≫ σ =
      Line.Fibers.pullSection L q (SecondNeutralParameterScheme.point A X) (q ≫ SecondNeutralParameterScheme.point A X) rfl (SecondNeutralParameterScheme.unitFrame A X L Dv).hom := by
    exact (congrArg (fun a => a ≫ σ)
      (Dv.unit_natural p (SecondNeutralParameterScheme.point A X) (p ≫ SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.point_neutral A X) ha rfl)).trans
      ((SecondNeutralTotalTransport.total_unit_neutral f g L Dh Dv Kh Kv hi ht _ _ ha hb himage).trans
        (Dv.unit_natural q (SecondNeutralParameterScheme.point A X) (q ≫ SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.point_neutral A X) hb rfl).symm)
  have hg : (overDatum f g L Dh Dv Kh Kv hcomm).hom base (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q hp hq =
      FiberBilinearGluing.fiberTransport L p q (SecondNeutralParameterScheme.point A X) σ := by
    exact (Recovered.OverSquare.pulledHom (f ⊗ₘ g) f (SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.point B Y) (SecondNeutralParameterScheme.point_naturality f g).symm
      (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) base p q hp hq).trans
      (FiberBilinearGluing.fiberTransport_eq_comp L p q (SecondNeutralParameterScheme.point A X) σ).symm
  rw [hg]
  exact FiberSectionGluing.section_gluing L p q (SecondNeutralParameterScheme.point A X) (SecondNeutralParameterScheme.unitFrame A X L Dv).hom σ hs

include hi ht in
/-- On the actual scheme kernel pair, the normalized original unit is invariant under the full geometric gluing. -/
theorem kernelPair_gluing :
    Bilinear.ContractionPullback.pulledSection (pullback.fst f.left f.left) (SecondNeutralParameterScheme.unitFrame A X L Dv).hom ≫
      (Geometric.CechInvariant.relationGluing f.left (ordinaryDatum f g L Dh Dv Kh Kv hcomm)).hom =
    Bilinear.ContractionPullback.pulledSection (pullback.snd f.left f.left) (SecondNeutralParameterScheme.unitFrame A X L Dv).hom :=
  normalized_gluing f g L Dh Dv Kh Kv hcomm hi ht (UnderlyingDescent.baseMap (Product.SquareTransport.testBase f))
    (Product.SquareTransport.firstPoint f) (Product.SquareTransport.secondPoint f)
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) (Product.SquareTransport.testBase f)
      (pullback.fst f.left f.left) pullback.condition)
    (UnderlyingDescent.coverMap_base (fun (_ : PUnit.{1}) => f) (i := PUnit.unit) (Product.SquareTransport.testBase f)
      (pullback.snd f.left f.left) rfl)

/-- The actual source-cover map obtained from the original normalized unit frame. -/
def coverUnit : (Scheme.Modules.pullback f.left).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) ⟶ Line.Fibers.fiber L (SecondNeutralParameterScheme.point A X) :=
  (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f.left).hom ≫ (SecondNeutralParameterScheme.unitFrame A X L Dv).hom

include hi ht in
/-- The genuine original unit supplies a compatible morphism from the quotient structure sheaf. -/
theorem coverUnit_compatible :
    (Scheme.Modules.pullback (pullback.fst f.left f.left)).map (coverUnit f L Dv) ≫
      (Geometric.CechInvariant.relationGluing f.left (ordinaryDatum f g L Dh Dv Kh Kv hcomm)).hom =
    (Cech.MateNormalization.standardGluing f.left (pullback.fst f.left f.left) (pullback.snd f.left f.left) pullback.condition).hom.app
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.left) ≫ (Scheme.Modules.pullback (pullback.snd f.left f.left)).map (coverUnit f L Dv) :=
  SectionDescentCompatibility.compatible f.left (pullback.fst f.left f.left) (pullback.snd f.left f.left)
    pullback.condition (SecondNeutralParameterScheme.unitFrame A X L Dv).hom _ (kernelPair_gluing f g L Dh Dv Kh Kv hcomm hi ht)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralUnitCompatibility
