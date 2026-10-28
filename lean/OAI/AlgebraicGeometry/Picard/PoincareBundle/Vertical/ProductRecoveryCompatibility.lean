import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.SquareTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery

/-! # Product Recovery Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductRecoveryCompatibility

noncomputable section

/-!
# Genuine vertical equivariance constructs the recovered vertical product's descent compatibility
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.SquareTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport (originalDatum firstPoint secondPoint point_images)
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {S : Scheme.{u}} {A B X Y : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)
  (hcomm : RectangularTransport.Commutes f g (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf
    (Biextension.AxisData.toAxisData f g L Dh Dv Kh Kv))

/-- The actual geometric datum for an input or output square. -/
def squareDatum (i : A ⊗ (X ⊗ X) ⟶ A ⊗ X) (j : B ⊗ (Y ⊗ Y) ⟶ B ⊗ Y)
    (hij : (f ⊗ₘ (g ⊗ₘ g)) ≫ j = i ≫ (f ⊗ₘ g)) :
    Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (f ⊗ₘ (g ⊗ₘ g)).left) :=
  Recovered.OverSquare.underlyingDatum (f ⊗ₘ g) (f ⊗ₘ (g ⊗ₘ g)) i j hij.symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm)

variable (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)
  (he : (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ g).left (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f ⊗ₘ g) (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm))).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)
      (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left) pullback.condition).hom.app R.sheaf ≫
        (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom)

/-- The actual compatible recovery of any one of the three quotient parameter line bundles. -/
def squareRecovery (i : A ⊗ (X ⊗ X) ⟶ A ⊗ X) (j : B ⊗ (Y ⊗ Y) ⟶ B ⊗ Y)
    (hij : (f ⊗ₘ (g ⊗ₘ g)) ≫ j = i ≫ (f ⊗ₘ g)) :
    (Scheme.Modules.pullback (f ⊗ₘ (g ⊗ₘ g)).left).obj (R.pullback j.left).sheaf ≅ Line.Fibers.fiber L i :=
  Recovered.OverSquare.recovery (f ⊗ₘ g) (f ⊗ₘ (g ⊗ₘ g)) i j hij.symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) R.sheaf e he

/-- Its kernel-pair compatibility is supplied by the constructed square recovery. -/
theorem squareRecovery_compatible (i : A ⊗ (X ⊗ X) ⟶ A ⊗ X) (j : B ⊗ (Y ⊗ Y) ⟶ B ⊗ Y)
    (hij : (f ⊗ₘ (g ⊗ₘ g)) ≫ j = i ≫ (f ⊗ₘ g)) :
    (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ (g ⊗ₘ g)).left (f ⊗ₘ (g ⊗ₘ g)).left)).map
        (squareRecovery f g L Dh Dv Kh Kv hcomm R e he i j hij).hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ (g ⊗ₘ g)).left (squareDatum f g L Dh Dv Kh Kv hcomm i j hij)).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ (g ⊗ₘ g)).left
      (pullback.fst (f ⊗ₘ (g ⊗ₘ g)).left (f ⊗ₘ (g ⊗ₘ g)).left)
      (pullback.snd (f ⊗ₘ (g ⊗ₘ g)).left (f ⊗ₘ (g ⊗ₘ g)).left) pullback.condition).hom.app (R.pullback j.left).sheaf ≫
      (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ (g ⊗ₘ g)).left (f ⊗ₘ (g ⊗ₘ g)).left)).map
        (squareRecovery f g L Dh Dv Kh Kv hcomm R e he i j hij).hom :=
  Recovered.OverSquare.recovery_compatible (f ⊗ₘ g) (f ⊗ₘ (g ⊗ₘ g)) i j hij.symm
    (Product.SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) R.sheaf e he

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central g Kv)
  (ht : Kernel.FramesTransverseTransport.Transverse f Kh Dv)

include hi hc ht in
/-- The original product and kernel laws imply the full product compatibility; no product-descent hypothesis is used. -/
theorem vertical_compatible :
    Bilinear.GlobalDescent.Compatible (f ⊗ₘ (g ⊗ₘ g)).left
      (squareDatum f g L Dh Dv Kh Kv hcomm (ProductParameters.outputPoint A X) (ProductParameters.outputPoint B Y) (ProductParameters.outputPoint_naturality f g))
      (R.pullback (ProductParameters.inputLeft B Y).left) (R.pullback (ProductParameters.inputRight B Y).left)
      (squareRecovery f g L Dh Dv Kh Kv hcomm R e he (ProductParameters.inputLeft A X) (ProductParameters.inputLeft B Y) (ProductParameters.inputLeft_naturality f g))
      (squareRecovery f g L Dh Dv Kh Kv hcomm R e he (ProductParameters.inputRight A X) (ProductParameters.inputRight B Y) (ProductParameters.inputRight_naturality f g))
      (ProductParameters.globalProduct A X L Dv) := by
  have hβ := ProductGluing.vertical_equivariance f g L Dh Dv Kh Kv hi hc ht
    (Product.SquareTransport.firstPoint (f ⊗ₘ (g ⊗ₘ g))) (Product.SquareTransport.secondPoint (f ⊗ₘ (g ⊗ₘ g))) (Product.SquareTransport.point_images (f ⊗ₘ (g ⊗ₘ g)))
  rw [← SquareTransport.relationGluing_transport f g L Dh Dv Kh Kv hcomm _ _ (ProductParameters.inputLeft_naturality f g),
    ← SquareTransport.relationGluing_transport f g L Dh Dv Kh Kv hcomm _ _ (ProductParameters.inputRight_naturality f g),
    ← SquareTransport.relationGluing_transport f g L Dh Dv Kh Kv hcomm _ _ (ProductParameters.outputPoint_naturality f g)] at hβ
  have h := Bilinear.RecoveryCompatibility.recovered_product_compatible
    (pullback.fst (f ⊗ₘ (g ⊗ₘ g)).left (f ⊗ₘ (g ⊗ₘ g)).left)
    (pullback.snd (f ⊗ₘ (g ⊗ₘ g)).left (f ⊗ₘ (g ⊗ₘ g)).left)
    (Line.Fibers.fiber_isLine L (ProductParameters.inputLeft A X)) (Line.Fibers.fiber_isLine L (ProductParameters.inputRight A X)) (ProductParameters.globalProduct A X L Dv)
    _ _ _ hβ.symm (f ⊗ₘ (g ⊗ₘ g)).left pullback.condition
    (R.pullback (ProductParameters.inputLeft B Y).left).sheaf (R.pullback (ProductParameters.inputRight B Y).left).sheaf
    (R.pullback (ProductParameters.inputLeft B Y).left).isLine (R.pullback (ProductParameters.inputRight B Y).left).isLine
    (squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (ProductParameters.inputLeft_naturality f g)).hom
    (squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (ProductParameters.inputRight_naturality f g)).hom
    (squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (ProductParameters.inputLeft_naturality f g))
    (squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (ProductParameters.inputRight_naturality f g))
  simp only [Bilinear.GlobalDescent.Compatible, Bilinear.GlobalDescent.coverMap,
    Tensor.LinePullback.pullbackIso, asIso_hom]
  simp only [Category.assoc] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductRecoveryCompatibility
