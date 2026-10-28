import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalAlternation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareSymmetry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Canonical Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.CanonicalAlternation.Construction

noncomputable section

/-! The original polarization constructs the symmetry and hence
alternation of the canonical CartierDuality pairing on every geometric fiber,
including all scheme-theoretic torsion in residue characteristic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)

set_option backward.isDefEq.respectTransparency false in
theorem geometricPoincarePolarizationSymmetry_exists :
    let B := (A.pullback s).scheme
    let P := Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) (PoincareSymmetry.Construction.geometricPolarizationMap D pol k s)
    ∃ σ : (Scheme.Modules.pullback (β_ B B).hom.left).obj P.sheaf ≅ P.sheaf,
      (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal B).left).mapIso σ =
        Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ B B).hom P (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal B)
          (DiagonalLineSymmetry.Construction.groupDiagonal_swap B) := by
  let B := (A.pullback s).scheme
  let P := Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine (D.pullback s) (PoincareSymmetry.Construction.geometricPolarizationMap D pol k s)
  have h := DiagonalLineSymmetry.Construction.existsUnique_diagonalLineSymmetry_of_iso B P
    (Classical.choice (Quotient.exact (Poincare.MultipleSymmetry.Construction.geometricOriginalPoincareLine_symmetry D pol k s)))
  obtain ⟨σ, hσ, _⟩ := h
  exact ⟨σ, hσ.trans (PoincareSymmetry.Construction.diagonalSymmetryComparison_eq_e45 _ _)⟩

def geometricPoincarePolarizationSymmetry := Classical.choose (geometricPoincarePolarizationSymmetry_exists D pol k s)

theorem geometricPoincarePolarizationSymmetry_diagonal :
    let B := (A.pullback s).scheme
    let P := Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine (D.pullback s)) (PoincareSymmetry.Construction.geometricPolarizationMap D pol k s)
    (Scheme.Modules.pullback (DiagonalLineSymmetry.Construction.groupDiagonal B).left).mapIso (geometricPoincarePolarizationSymmetry D pol k s) =
      Picard.PoincareBundle.Pulled.LineBilinear.fiberComparison (β_ B B).hom P (DiagonalLineSymmetry.Construction.groupDiagonal B) (DiagonalLineSymmetry.Construction.groupDiagonal B)
        (DiagonalLineSymmetry.Construction.groupDiagonal_swap B) :=
  Classical.choose_spec (geometricPoincarePolarizationSymmetry_exists D pol k s)

theorem geometricCanonicalPolarizationPairing_alternating (n : ℕ) (hn : 0 < n)
    {Q : Over (Spec (.of k))} (x : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).pairValue x x = 1 :=
  IsogenyQuotient.Field.CanonicalAlternation.Construction.fieldNativePolarizationPairing_alternating_of_symmetry (D.pullback s) (pol.pullback s) n hn
    (geometricPoincarePolarizationSymmetry D pol k s) (geometricPoincarePolarizationSymmetry_diagonal D pol k s) x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.CanonicalAlternation.Construction
