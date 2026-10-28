import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RecoveryCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.DescentRecovery

/-! # Recovery Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoveryCompatibility

noncomputable section

/-!
# Genuine product equivariance constructs the recovered product's descent compatibility
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.ParameterSchemes OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.SquareTransport
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
def squareDatum (i : (A ⊗ A) ⊗ X ⟶ A ⊗ X) (j : (B ⊗ B) ⊗ Y ⟶ B ⊗ Y)
    (hij : ((f ⊗ₘ f) ⊗ₘ g) ≫ j = i ≫ (f ⊗ₘ g)) :
    Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => ((f ⊗ₘ f) ⊗ₘ g).left) :=
  Recovered.OverSquare.underlyingDatum (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij.symm
    (SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm)

variable (R : Line.Bundles.LineBundle (B ⊗ Y).left)
  (e : (Scheme.Modules.pullback (f ⊗ₘ g).left).obj R.sheaf ≅ L.sheaf)
  (he : (Scheme.Modules.pullback (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom ≫
      (Geometric.CechInvariant.relationGluing (f ⊗ₘ g).left (UnderlyingDescent.underlyingDatum Geometric.KernelLinearization.modulePullbacks
        (fun (_ : PUnit.{1}) => f ⊗ₘ g) (SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm))).hom =
    (Cech.MateNormalization.standardGluing (f ⊗ₘ g).left (pullback.fst (f ⊗ₘ g).left (f ⊗ₘ g).left)
      (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left) pullback.condition).hom.app R.sheaf ≫
        (Scheme.Modules.pullback (pullback.snd (f ⊗ₘ g).left (f ⊗ₘ g).left)).map e.hom)

/-- The actual compatible recovery of any one of the three quotient parameter line bundles. -/
def squareRecovery (i : (A ⊗ A) ⊗ X ⟶ A ⊗ X) (j : (B ⊗ B) ⊗ Y ⟶ B ⊗ Y)
    (hij : ((f ⊗ₘ f) ⊗ₘ g) ≫ j = i ≫ (f ⊗ₘ g)) :
    (Scheme.Modules.pullback ((f ⊗ₘ f) ⊗ₘ g).left).obj (R.pullback j.left).sheaf ≅ Line.Fibers.fiber L i :=
  Recovered.OverSquare.recovery (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij.symm
    (SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) R.sheaf e he

/-- Its kernel-pair compatibility is supplied by the constructed square recovery. -/
theorem squareRecovery_compatible (i : (A ⊗ A) ⊗ X ⟶ A ⊗ X) (j : (B ⊗ B) ⊗ Y ⟶ B ⊗ Y)
    (hij : ((f ⊗ₘ f) ⊗ₘ g) ≫ j = i ≫ (f ⊗ₘ g)) :
    (Scheme.Modules.pullback (pullback.fst ((f ⊗ₘ f) ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left)).map
        (squareRecovery f g L Dh Dv Kh Kv hcomm R e he i j hij).hom ≫
      (Geometric.CechInvariant.relationGluing ((f ⊗ₘ f) ⊗ₘ g).left (squareDatum f g L Dh Dv Kh Kv hcomm i j hij)).hom =
    (Cech.MateNormalization.standardGluing ((f ⊗ₘ f) ⊗ₘ g).left
      (pullback.fst ((f ⊗ₘ f) ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left)
      (pullback.snd ((f ⊗ₘ f) ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left) pullback.condition).hom.app (R.pullback j.left).sheaf ≫
      (Scheme.Modules.pullback (pullback.snd ((f ⊗ₘ f) ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left)).map
        (squareRecovery f g L Dh Dv Kh Kv hcomm R e he i j hij).hom :=
  Recovered.OverSquare.recovery_compatible (f ⊗ₘ g) ((f ⊗ₘ f) ⊗ₘ g) i j hij.symm
    (SquareTransport.originalDatum f g L Dh Dv Kh Kv hcomm) R.sheaf e he

variable (hi : Biextension.Compatibility.Interchange L Dh Dv)
  (hc : KernelFrame.Centrality.Central f Kh)
  (ht : Kernel.FramesTransverseTransport.Transverse g Kv Dh)

include hi hc ht in
/-- The original product and kernel laws imply the full product compatibility; no product-descent hypothesis is used. -/
theorem horizontal_compatible :
    Bilinear.GlobalDescent.Compatible ((f ⊗ₘ f) ⊗ₘ g).left
      (squareDatum f g L Dh Dv Kh Kv hcomm (ParameterSchemes.outputPoint A X) (ParameterSchemes.outputPoint B Y) (ParameterSchemes.outputPoint_naturality f g))
      (R.pullback (ParameterSchemes.inputLeft B Y).left) (R.pullback (ParameterSchemes.inputRight B Y).left)
      (squareRecovery f g L Dh Dv Kh Kv hcomm R e he (ParameterSchemes.inputLeft A X) (ParameterSchemes.inputLeft B Y) (ParameterSchemes.inputLeft_naturality f g))
      (squareRecovery f g L Dh Dv Kh Kv hcomm R e he (ParameterSchemes.inputRight A X) (ParameterSchemes.inputRight B Y) (ParameterSchemes.inputRight_naturality f g))
      (ParameterSchemes.globalProduct A X L Dh) := by
  have hβ := TransportGluing.horizontal_equivariance f g L Dh Dv Kh Kv hi hc ht
    (SquareTransport.firstPoint ((f ⊗ₘ f) ⊗ₘ g)) (SquareTransport.secondPoint ((f ⊗ₘ f) ⊗ₘ g)) (SquareTransport.point_images ((f ⊗ₘ f) ⊗ₘ g))
  rw [← SquareTransport.relationGluing_transport f g L Dh Dv Kh Kv hcomm _ _ (ParameterSchemes.inputLeft_naturality f g),
    ← SquareTransport.relationGluing_transport f g L Dh Dv Kh Kv hcomm _ _ (ParameterSchemes.inputRight_naturality f g),
    ← SquareTransport.relationGluing_transport f g L Dh Dv Kh Kv hcomm _ _ (ParameterSchemes.outputPoint_naturality f g)] at hβ
  have h := Bilinear.RecoveryCompatibility.recovered_product_compatible
    (pullback.fst ((f ⊗ₘ f) ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left)
    (pullback.snd ((f ⊗ₘ f) ⊗ₘ g).left ((f ⊗ₘ f) ⊗ₘ g).left)
    (Line.Fibers.fiber_isLine L (ParameterSchemes.inputLeft A X)) (Line.Fibers.fiber_isLine L (ParameterSchemes.inputRight A X)) (ParameterSchemes.globalProduct A X L Dh)
    _ _ _ hβ.symm ((f ⊗ₘ f) ⊗ₘ g).left pullback.condition
    (R.pullback (ParameterSchemes.inputLeft B Y).left).sheaf (R.pullback (ParameterSchemes.inputRight B Y).left).sheaf
    (R.pullback (ParameterSchemes.inputLeft B Y).left).isLine (R.pullback (ParameterSchemes.inputRight B Y).left).isLine
    (squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (ParameterSchemes.inputLeft_naturality f g)).hom
    (squareRecovery f g L Dh Dv Kh Kv hcomm R e he _ _ (ParameterSchemes.inputRight_naturality f g)).hom
    (squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (ParameterSchemes.inputLeft_naturality f g))
    (squareRecovery_compatible f g L Dh Dv Kh Kv hcomm R e he _ _ (ParameterSchemes.inputRight_naturality f g))
  simp only [Bilinear.GlobalDescent.Compatible, Bilinear.GlobalDescent.coverMap,
    Tensor.LinePullback.pullbackIso, asIso_hom]
  simp only [Category.assoc] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.RecoveryCompatibility
