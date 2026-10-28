import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.GlobalKernelIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Isotropic.InducingLineDescent

/-! # Isotropic Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.IsotropicLineDescent

noncomputable section

/-! Scheme-valued canonical kernel isotropy descends an inducing line without auxiliary global frame or translation assumptions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

variable {k : Type u} [Field k] [IsAlgClosed k] {A B : Over (Spec (.of k))}
  [GrpObj A] [IsCommMonObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] [IsLocallyNoetherian B.left]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [Surjective f.left]
  (Q : Line.Bundles.LineBundle (A ⊗ A).left)
  (D : FiberwiseMultiplication.Multiplication (fst A A) (snd A A) Q)
  (K : FiberwiseMultiplication.KernelFrames (fst A A) (snd A A) Q f D)
  (Dv : FiberwiseMultiplication.Multiplication (snd A A) (fst A A) Q)
  (σ : (Scheme.Modules.pullback (β_ A A).hom.left).obj Q.sheaf ≅ Q.sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication Q D σ = Dv)
  (L : Line.Bundles.LineBundle A.left)
  (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (Line.Fibers.fiber L (fst A A))) (Line.Fibers.fiber L (snd A A)) ≅ Line.Fibers.fiber L μ[A])
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber L η[A])

include e o

/-- Smooth connected proper group geometry supplies integrality; canonical isotropy supplies the global obstruction equality. -/
theorem exists_descended_line
    (hσ : (Scheme.Modules.pullback (AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A).left).mapIso σ =
      AbelianScheme.IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A (Line.Comparison.Bundle.toShared Q))
    (hi : Biextension.Compatibility.Isotropic Q D Dv f f K
      (Symmetric.TransverseFrames.secondFramesOfCompatible Q D Dv σ f K hv)) :
    ∃ M : Line.Bundles.LineBundle B.left,
      Nonempty ((Scheme.Modules.pullback f.left).obj M.sheaf ≅ L.sheaf) := by
  have : IsIntegral A.left := Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group A
  exact Isotropic.InducingLineDescent.exists_descended_line_of_diagonal f (Line.Comparison.Bundle.toShared Q) L e
    (KernelFrame.Global.globalFrame f Q D K) σ o hσ
    (GlobalKernelIsotropy.isotropic f Q D K Dv σ hv hi)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.IsotropicLineDescent
