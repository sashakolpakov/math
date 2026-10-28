import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicLineDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingLineFormulaTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupHomAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointLineBundleTriviality

/-! # Isotropic Ample Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicAmpleDescent

noncomputable section

/-! An actual ample line on the quotient has an inducing formula whose pullback is the prescribed multiple of the original Poincare family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupHomAmpleness.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  (ell : A.scheme ⟶ D.abelian.scheme) [IsMonHom ell] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) ell).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf))
  (n : ℕ) (hn : 0 < n) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (PairingIndependence.ReferenceTorsion.pairing D ell L hformula n))

include hn hlag

/-- Positive powers, canonical isotropy, effective line descent, and finite-flat ampleness descent construct this line and formula. -/
theorem exists_ample_inducing_pullback
    (hp : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincare.pullback (ell ⊗ₘ 𝟙 A.scheme).left)) :
    ∃ N : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.scheme.left,
      N.IsAmple ∧ Nonempty ((N.pullback η[B.scheme].left).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) ∧
      Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
        (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) (ell ^ n)).sheaf
          ((N.pullback f.hom.left).pullback (fst A.scheme A.scheme).left).sheaf)
        ((N.pullback f.hom.left).pullback (snd A.scheme A.scheme).left).sheaf ≅
          ((N.pullback f.hom.left).pullback μ[A.scheme].left).sheaf) := by
  obtain ⟨M, hM, ⟨o⟩, ⟨formula⟩⟩ := PositivePoincareMultiple.positive_multiple
    (Line.Comparison.Bundle.fromShared D.poincare) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D) ell hp n hn
  obtain ⟨N, ⟨e⟩⟩ := IsotropicLineDescent.exists_descended_line
    D ell L hformula n f hf hlag (Line.Comparison.Bundle.fromShared M) formula o.symm
  have : IsIntegral A.scheme.left := Homomorphisms.GroupRigidity.Construction.integral_smooth_proper_connected_group A.scheme
  have : ConnectedSpace B.scheme.left := f.hom.left.surjective.connectedSpace f.hom.left.continuous
  have : IsLocallyNoetherian B.scheme.left := LocallyOfFiniteType.isLocallyNoetherian B.scheme.hom
  have hN : (Line.Comparison.Bundle.toShared N).IsAmple := AbelianScheme.IsogenyQuotient.GroupHomAmpleness.Construction.finiteFlat_groupHom_isAmple_of_pullback f.hom (Line.Comparison.Bundle.toShared N)
    (hM.of_iso e.symm)
  refine ⟨Line.Comparison.Bundle.toShared N, hN, ?_, ⟨?_⟩⟩
  · have : Subsingleton (𝟙_ (Over (Spec (.of k)))).left :=
      inferInstanceAs (Subsingleton (Spec (.of k)))
    have : Nonempty (𝟙_ (Over (Spec (.of k)))).left :=
      inferInstanceAs (Nonempty (Spec (.of k)))
    exact ((Line.Comparison.Bundle.toShared N).pullback η[B.scheme].left).exists_trivialization_of_subsingleton
  · exact InducingLineFormulaTransport.formula A.scheme
      (D.poincare.pullback ((ell ^ n) ⊗ₘ 𝟙 A.scheme).left) M ((Line.Comparison.Bundle.toShared N).pullback f.hom.left) e.symm formula

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.IsotropicAmpleDescent
