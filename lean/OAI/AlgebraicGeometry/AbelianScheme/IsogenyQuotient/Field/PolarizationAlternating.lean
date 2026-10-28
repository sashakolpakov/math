import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalAlternation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PositiveFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.Symmetry

/-! # Polarization Alternating -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating.Construction

noncomputable section

/-! The original geometric polarization itself supplies the normalized
symmetry proving alternation on every scheme-valued torsion point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

set_option backward.isDefEq.respectTransparency false in
theorem fieldNativePolarizationPairing_alternating (T : Over (Spec (.of k)))
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  obtain ⟨L, _ha, _h0, hformula⟩ := Picard.PoincareBundle.Reference.PositiveFormula.of_polarization D pol
  have hs := DiagonalLineSymmetry.Construction.existsUnique_diagonalLineSymmetry A.scheme
    (Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D pol.isogeny.hom) L hformula
  obtain ⟨σ, hσ, _⟩ := hs
  exact CanonicalAlternation.Construction.fieldNativePolarizationPairing_alternating_of_symmetry D pol n hn σ
    (hσ.trans (Picard.PoincareBundle.Reference.Symmetry.ReferencePoincare.diagonal_comparison A.scheme
      (Poincare.MultipleSymmetry.Construction.originalPoincareFamilyLine D pol.isogeny.hom))) x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating.Construction
