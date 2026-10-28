import OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedFamilyIsomorphism
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.SecondUnitFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.Map

/-! # Family Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.FamilyIso.Family

noncomputable section

/-!
# The normalized unit on the actual canonical descended Poincare line
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.LineDescent OAI.AlgebraicGeometry.Picard.PoincareBundle.SecondNeutralParameterScheme

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  {A Z : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)
  (hi : Biextension.Compatibility.Interchange P Dh Dv) (f : A ⟶ B.scheme) [IsMonHom f] (hφ : Kernel.Scheme.kernelInclusion f ≫ φ = 1)
  (symmetry : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P φ).sheaf ≅ (FirstBiextensionFactor.familyLine P φ).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) symmetry = Poincare.TransverseFrames.sourceVertical φ P Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P φ) (Poincare.TransverseFrames.sourceVertical φ P Dv) symmetry =
    Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh)
  (he : Biextension.Compatibility.Isotropic (FirstBiextensionFactor.familyLine P φ) (Pulled.KernelFrames.Poincare.sourceMultiplication φ P Dh) (Poincare.TransverseFrames.sourceVertical φ P Dv)
    f f (Pulled.KernelFrames.Poincare.kernelFrames φ P Dh f hφ) (LineDescent.secondKernelFrames φ P Dh Dv f hφ symmetry hv))
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  [IsLocallyNoetherian (B.scheme ⊗ B.scheme).left]
  [IsLocallyNoetherian (B.scheme ⊗ (B.scheme ⊗ B.scheme)).left] [IsLocallyNoetherian B.scheme.left]

variable (DB : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B.scheme)
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian B.scheme) (fst DB.abelian B.scheme)
    (Line.Comparison.Bundle.fromShared DB.poincare))

include Qv

/-- The constructed quotient line is an actual Poincare family for its represented quotient map. -/
theorem exists_familyIso :
    Nonempty ((LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he).sheaf ≅
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DB.poincare)
        (Map.representedMap φ P Dh Dv hi f hφ symmetry hv hh he
          (SharedRepresentation.representation DB))).sheaf) := by
  have : CompactSpace B.scheme.left := QuasiCompact.compactSpace_of_compactSpace B.scheme.hom
  have : QuasiSeparatedSpace B.scheme.left := quasiSeparatedSpace_of_quasiSeparated B.scheme.hom
  obtain ⟨e, _⟩ := RepresentedFamilyIsomorphism.Family.normalized_iso B DB
    (LineDescent.descendedLine φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product φ P Dh Dv hi f hφ symmetry hv hh he)
    (VerticalProduct.product_isIso φ P Dh Dv hi f hφ symmetry hv hh he)
    (Vertical.ProductParameters.globalProduct DB.abelian B.scheme (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
    (Vertical.ProductParameters.globalProduct_isIso DB.abelian B.scheme (Line.Comparison.Bundle.fromShared DB.poincare) Qv)
    (SecondUnitFrame.unitFrame φ P Dh Dv hi f hφ symmetry hv hh he).symm
  exact ⟨e⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CanonicalPoincare.FamilyIso.Family
