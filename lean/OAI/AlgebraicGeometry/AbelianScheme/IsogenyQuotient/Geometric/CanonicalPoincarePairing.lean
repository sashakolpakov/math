import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPoincarePairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.CanonicalAlternation
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.PoincareLine

/-! # Canonical Poincare Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.CanonicalPoincarePairing.Construction

noncomputable section

/-! On every geometric fiber, the original polarization identifies
the canonical CartierDuality pairing with the actual PoincareBundle Poincare pairing. All
symmetries, products, and compatibility laws are constructed here from
the original data. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

variable {S : Scheme} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)
  (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S) (n : ℕ) (hn : 0 < n)

theorem geometricCanonicalPolarizationPairing_eq_poincare :
    IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn =
      PoincareLine.Construction.geometricPoincareNativeTorsionPairing D pol k s n :=
  IsogenyQuotient.Field.CanonicalPoincarePairing.Construction.fieldCanonicalPairing_eq_poincare (D.pullback s) (pol.pullback s) n hn
    (CanonicalAlternation.Construction.geometricPoincarePolarizationSymmetry D pol k s) (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry D pol k s n)
    (CanonicalAlternation.Construction.geometricPoincarePolarizationSymmetry_diagonal D pol k s) (PoincareSymmetry.Construction.geometricPoincareMultipleSymmetry_diagonal D pol k s n)
    (PoincareLine.Construction.geometricPoincareMultiplications_symmetry_vertical D pol k s n)
    (PoincareLine.Construction.geometricPoincareMultiplications_symmetry_horizontal D pol k s n)

theorem geometricCanonicalPolarizationPairing_poincare_value {Q : Over (Spec (.of k))}
    (x y : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme (A.pullback s).scheme n) :
    (IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing (A.pullback s) (D.pullback s) (pol.pullback s) n hn).pairValue x y =
      (PoincareLine.Construction.geometricPoincareNativeTorsionPairing D pol k s n).pairValue x y :=
  congrArg (fun e => e.pairValue x y) (geometricCanonicalPolarizationPairing_eq_poincare D pol k s n hn)

include hn in
theorem geometricPoincarePairing_isPerfect_of_coprime (hc : Nat.Coprime n ((∏ i, δ i) ^ 2)) :
    (PoincareLine.Construction.geometricPoincareNativeTorsionPairing D pol k s n).toSheafPairing.IsPerfect := by
  rw [← geometricCanonicalPolarizationPairing_eq_poincare D pol k s n hn]
  exact IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing_isPerfect (A.pullback s) (D.pullback s) (pol.pullback s) n hn hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.CanonicalPoincarePairing.Construction
