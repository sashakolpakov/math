import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalAlternation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

/-! # Reference Field Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceFieldAlternation.Construction

noncomputable section

/-! The original polarization itself constructs the normalized symmetry
needed for alternation over the actual algebraically closed source field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalAlternation.Construction OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

theorem originalPolarizationFamilySymmetry_exists :
    ∃ σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
        (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf ≅
          (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf,
      (Scheme.Modules.pullback (IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
        Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ A.scheme A.scheme).hom
          (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom)
          (IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme) (IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal_swap A.scheme) := by
  have hs := (Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare.existsUnique_symmetry D pol.isogeny.hom
    (Picard.PoincareBundle.PolarizationTorsionPairing.inducingLine D pol)
    (Picard.PoincareBundle.PolarizationTorsionPairing.inducingLine_formula D pol) 1).exists
  have ht : ∃ σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf ≅
        (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) pol.isogeny.hom).sheaf,
    (Scheme.Modules.pullback (IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
      IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A.scheme (IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D pol.isogeny.hom) := by
    exact (congrArg (fun f : A.scheme ⟶ D.abelian.scheme =>
      ∃ σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
          (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f).sheaf ≅
            (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (IsogenyQuotient.Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) f).sheaf,
        (Scheme.Modules.pullback (IsogenyQuotient.DiagonalLineSymmetry.Construction.groupDiagonal A.scheme).left).mapIso σ =
          IsogenyQuotient.DiagonalLineSymmetry.Construction.diagonalSymmetryComparison A.scheme (IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D f))
      (pow_one pol.isogeny.hom)).mp hs
  obtain ⟨σ, hσ⟩ := ht
  exact ⟨σ, hσ.trans (Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare.diagonal_comparison A.scheme
    (IsogenyQuotient.Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D pol.isogeny.hom))⟩

theorem originalFieldPolarizationPairing_alternating (n : ℕ) (hn : 0 < n)
    {T : Over (Spec (.of k))} (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  obtain ⟨σ, hd⟩ := originalPolarizationFamilySymmetry_exists D pol
  exact IsogenyQuotient.Field.CanonicalAlternation.Construction.fieldNativePolarizationPairing_alternating_of_symmetry D pol n hn σ hd x

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceFieldAlternation.Construction
