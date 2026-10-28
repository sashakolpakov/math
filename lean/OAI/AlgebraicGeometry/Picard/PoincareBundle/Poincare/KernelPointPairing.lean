import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.IntrinsicPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PointComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.ScalarLineIso

/-! # Kernel Point Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelPointPairing

noncomputable section

/-! The actual Poincare line of the included dual kernel point realizes the canonical kernel pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Global
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.FramesTransverseTransport OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {k : Type u} [Field k] {A B : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj B] (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (φ : A ⟶ D.abelian) [IsMonHom φ]
  (Dh : FiberwiseMultiplication.Multiplication (fst D.abelian A) (snd D.abelian A) (Line.Comparison.Bundle.fromShared D.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd D.abelian A) (fst D.abelian A) (Line.Comparison.Bundle.fromShared D.poincare))
  (hp : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared D.poincare) Dh Dv)
  (n : ℕ) [IsAffine (Kernel.Scheme.kernelObject ((𝟙 A) ^ n)).left]
  (f : A ⟶ B) [IsMonHom f]
  (Kh : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (φ ^ n)) f
    (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.poincare) Dh))
  (J : FiberwiseMultiplication.KernelFrames (snd A A) (fst A A) (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (φ ^ n)) ((𝟙 A) ^ n)
    (TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.poincare) Dv))
  (hKh : Kernel.FramesTransverseTransport.Transverse f Kh (TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.poincare) Dv))
  (hJ : Kernel.FramesTransverseTransport.Transverse ((𝟙 A) ^ n) J (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.poincare) Dh))

include hp hKh hJ

/-- A constructed actual frame of the point's Poincare line has inverse canonical pairing as its scalar. -/
theorem exists_frame_character :
    ∃ e : (Scheme.Modules.pullback (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n).left).obj
        (PointNormalization.line D (Kernel.Scheme.kernelInclusion f ≫ φ)).sheaf ≅
          AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Kernel.Scheme.kernelObject f ⊗ A).left,
      ∀ (T : Over (Spec (.of k))) (a : T ⟶ Kernel.Scheme.kernelObject f) (b : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n))
        (z w : T ⟶ A) (_h : (b ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) * z = w)
        (q : T ⟶ Kernel.Scheme.kernelObject f ⊗ A)
        (hz : lift a z ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n) = q)
        (hw : lift a w ≫ (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n) = q),
        Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
          (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n).left
            (PointNormalization.line D (Kernel.Scheme.kernelInclusion f ≫ φ)).sheaf) e
          q.left (lift a z).left (lift a w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
          (ConcreteKernelPairing.Concrete.value f ((𝟙 A) ^ n) (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (φ ^ n))
            (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) (Line.Comparison.Bundle.fromShared D.poincare) Dh)
            (TransverseFrames.sourceVertical (φ ^ n) (Line.Comparison.Bundle.fromShared D.poincare) Dv) Kh J a b)⁻¹.val := by
  obtain ⟨s, hs⟩ := IntrinsicPairing.Intrinsic.exists_frame_character φ (Line.Comparison.Bundle.fromShared D.poincare)
    Dh Dv hp n f Kh J hKh hJ
  let e := PointComposition.iso D φ (Kernel.Scheme.kernelInclusion f)
  refine ⟨Canonical.ScalarLineIso.frame (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n).left e s, ?_⟩
  intro T a b z w h q hz hw
  exact (Canonical.ScalarLineIso.scalar_eq (𝟙 (Kernel.Scheme.kernelObject f) ⊗ₘ (𝟙 A) ^ n).left e s
    q.left (lift a z).left (lift a w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw)).trans
      (hs T a b z w h q hz hw)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.KernelPointPairing
