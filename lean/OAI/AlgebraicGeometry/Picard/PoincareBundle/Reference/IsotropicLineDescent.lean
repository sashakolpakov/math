import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.IsotropicLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence

/-! # Isotropic Line Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicLineDescent

noncomputable section

/-! The original Poincare data and full torsion self-annihilation descend every normalized inducing line for the required multiple. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf))
  (n : ℕ) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (PairingIndependence.ReferenceTorsion.pairing D ell L hformula n))
  (M : Line.Bundles.LineBundle A.scheme.left)
  (formula : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)).sheaf (Line.Fibers.fiber M (fst A.scheme A.scheme)))
    (Line.Fibers.fiber M (snd A.scheme A.scheme)) ≅ Line.Fibers.fiber M μ[A.scheme])
  (o : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅ Line.Fibers.fiber M η[A.scheme])

include formula o hlag

/-- All global frames, normalized symmetry, translation and cocycle data are constructed from the original Poincare bundle. -/
theorem exists_descended_line :
    ∃ N : Line.Bundles.LineBundle B.scheme.left,
      Nonempty ((Scheme.Modules.pullback f.hom.left).obj N.sheaf ≅ M.sheaf) := by
  have : IsLocallyNoetherian B.scheme.left := LocallyOfFiniteType.isLocallyNoetherian B.scheme.hom
  let ha := Poincare.TorsionKernelFrame.multiple_annihilates_kernel f.hom ell n hf
  exact Canonical.IsotropicLineDescent.exists_descended_line f.hom
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D))
    (Pulled.KernelFrames.Poincare.kernelFrames (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) f.hom ha)
    (Poincare.TransverseFrames.sourceVertical (ell ^ n) (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D))
    (Symmetry.ReferencePoincare.symmetry D ell L hformula n) (Symmetry.ReferencePoincare.symmetry_vertical D ell L hformula n) M formula o
    (Symmetry.ReferencePoincare.symmetry_diagonal D ell L hformula n)
    (TorsionPairing.Poincare.kernel_isotropic ell (Line.Comparison.Bundle.fromShared D.poincare)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D) n
      (Symmetry.ReferencePoincare.symmetry D ell L hformula n) (Symmetry.ReferencePoincare.symmetry_vertical D ell L hformula n)
      (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange D) (Symmetry.ReferencePoincare.symmetry_horizontal D ell L hformula n) f.hom hf hlag)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicLineDescent
