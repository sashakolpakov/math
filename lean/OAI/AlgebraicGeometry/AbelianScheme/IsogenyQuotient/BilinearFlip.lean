import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearPullbackAdjunction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Bilinear Flip -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearFlip.Construction

noncomputable section

/-! Exchange the two inputs of an actual bilinear sheaf map. The
exchange commutes with geometric pullback and all fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.PullbackMap

universe u

variable {X : Scheme.{u}} {M N P M' N' P' : X.Modules}

def flipLineBilinear (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap N M P where
  app U := (b.app U).flip
  naturality h x y := b.naturality h y x

theorem flipLineBilinear_flip (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) : flipLineBilinear (flipLineBilinear b) = b := by
  ext U x y
  rfl

theorem flipLineBilinear_postcomp (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (f : P ⟶ P') :
    flipLineBilinear (b.postcomp f) = (flipLineBilinear b).postcomp f := by
  ext U x y
  rfl

theorem flipLineBilinear_precomp (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (f : M' ⟶ M) (g : N' ⟶ N) :
    flipLineBilinear (b.precomp f g) = (flipLineBilinear b).precomp g f := by
  ext U x y
  rfl

theorem flipLineBilinear_transport (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (f : M ≅ M') (g : N ≅ N') (h : P ≅ P') :
    flipLineBilinear (Picard.PoincareBundle.Bilinear.Transport.transport b f g h) =
      Picard.PoincareBundle.Bilinear.Transport.transport (flipLineBilinear b) g f h := by
  ext U x y
  rfl

theorem flipLineBilinear_pushforward {Y : Scheme.{u}} (f : X ⟶ Y) (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    flipLineBilinear (b.pushforward f) = (flipLineBilinear b).pushforward f := by
  ext U x y
  rfl

theorem flipLineBilinear_bilinearAdjoint {Y : Scheme.{u}} (f : X ⟶ Y) (L K : Y.Modules)
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj K) P) :
    flipLineBilinear (Picard.PoincareBundle.Tensor.PullbackMap.bilinearAdjoint f L K b) = Picard.PoincareBundle.Tensor.PullbackMap.bilinearAdjoint f K L (flipLineBilinear b) := by
  ext U x y
  rfl

theorem flipLineBilinear_pullback {Y : Scheme.{u}} (f : Y ⟶ X)
    (hM : Picard.PoincareBundle.Line.Bundles.IsLine M) (hN : Picard.PoincareBundle.Line.Bundles.IsLine N) (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) :
    flipLineBilinear (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hM hN b) =
      Picard.PoincareBundle.Bilinear.BilinearPullback.pullback f hN hM (flipLineBilinear b) := by
  apply BilinearPullbackAdjunction.Construction.bilinearAdjoint_injective f N M hN hM
  dsimp only
  rw [← flipLineBilinear_bilinearAdjoint, BilinearPullbackAdjunction.Construction.bilinearAdjoint_pullback,
    BilinearPullbackAdjunction.Construction.bilinearAdjoint_pullback, flipLineBilinear_postcomp]

theorem flipLineBilinear_pullBilinear {S : Scheme.{u}} {E T U : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : U ⟶ T)
    (x y z : T ⟶ E) (x' y' z' : U ⟶ E) (hx : r ≫ x = x') (hy : r ≫ y = y') (hz : r ≫ z = z')
    (b : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L y) (Picard.PoincareBundle.Line.Fibers.fiber L z)) :
    flipLineBilinear (Picard.PoincareBundle.Line.Fibers.pullBilinear L r x y z x' y' z' hx hy hz b) =
      Picard.PoincareBundle.Line.Fibers.pullBilinear L r y x z y' x' z' hy hx hz (flipLineBilinear b) := by
  unfold Picard.PoincareBundle.Line.Fibers.pullBilinear
  rw [flipLineBilinear_transport, flipLineBilinear_pullback]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BilinearFlip.Construction
