import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionTypedIsogeny

/-! # Typed Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.TypedDescent

noncomputable section

/-! The original inducing-line formula suffices for unique type-preserving isogeny descent through a self-annihilating full torsion kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A DA.abelian) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (δ : Fin a → ℕ) (ht : ell.HasPolarizationType δ)
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
  (hformula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) ell.hom).sheaf (L.pullback (fst A.scheme A.scheme).left).sheaf)
    (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf))
  (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (PairingIndependence.ReferenceTorsion.pairing DA ell.hom L hformula n))

include ht hn hnd hf hlag

/-- All Poincare products, symmetry, compatibility, recovery and kernel comparisons are constructed from the original data. -/
theorem existsUnique_isogeny : ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
    f.hom ≫ m.hom ≫ DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = ell.hom ^ n ∧
    m.HasPolarizationType δ :=
  SharedTorsionTypedIsogeny.existsUnique_isogeny DA DB ell f δ ht n hn hnd hf
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication DA) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication DA)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication DB) (AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication DB)
    (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange DA) (AbelianScheme.IsogenyQuotient.Reference.PoincareInterchange.Construction.originalPoincareMultiplications_interchange DB)
    (Symmetry.ReferencePoincare.symmetry DA ell.hom L hformula n) (Symmetry.ReferencePoincare.symmetry_vertical DA ell.hom L hformula n)
    (Symmetry.ReferencePoincare.symmetry_horizontal DA ell.hom L hformula n) hlag

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.TypedDescent
