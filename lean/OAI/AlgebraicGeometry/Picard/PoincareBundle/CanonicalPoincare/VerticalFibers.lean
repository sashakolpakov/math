import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalProduct
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterRecovery

/-! # Vertical Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalFibers

noncomputable section

/-!
# Actual vertical quotient-fiber products from canonical Poincare descent
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters

variable {S : Scheme.{u}} {A B Z : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hi : Biextension.Compatibility.Interchange P Dh Dv) (f : A ⟶ B) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) symmetry = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv))
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B ⊗ B).left] [IsLocallyNoetherian (B ⊗ (B ⊗ B)).left]

/-- The constructed global quotient product supplies a genuine product on every quotient test-scheme fiber. -/
def product {T : Over S} (a b c : T ⟶ B ⊗ B) (h : FiberwiseMultiplication.ProductRel (snd B B) (fst B B) a b c) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
      (Line.Fibers.fiber (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he) a)
      (Line.Fibers.fiber (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he) b)
      (Line.Fibers.fiber (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he) c) :=
  Vertical.ParameterRecovery.product (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he) a b c h

/-- Every constructed quotient fiber product is a bilinear line-bundle isomorphism. -/
theorem product_isIso {T : Over S} (a b c : T ⟶ B ⊗ B) (h : FiberwiseMultiplication.ProductRel (snd B B) (fst B B) a b c) :
    IsIso (Bilinear.BilinearPullback.toHom (product φ P Dh Dv hi f hφ symmetry hv hh he a b c h)) :=
  Vertical.ParameterRecovery.product_isIso (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he) a b c h

/-- These actual quotient products commute with every scheme-valued change of test object. -/
theorem product_natural {T U : Over S} (t : U ⟶ T) (a b c : T ⟶ B ⊗ B)
    (h : FiberwiseMultiplication.ProductRel (snd B B) (fst B B) a b c) (a' b' c' : U ⟶ B ⊗ B)
    (h' : FiberwiseMultiplication.ProductRel (snd B B) (fst B B) a' b' c')
    (ha : t ≫ a = a') (hb : t ≫ b = b') (hc : t ≫ c = c') :
    Line.Fibers.pullBilinear (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
      t a b c a' b' c' ha hb hc (product φ P Dh Dv hi f hφ symmetry hv hh he a b c h) =
        product φ P Dh Dv hi f hφ symmetry hv hh he a' b' c' h' :=
  Vertical.ParameterRecovery.product_natural (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he) t a b c h a' b' c' h' ha hb hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.VerticalFibers
