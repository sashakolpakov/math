import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PairingReflection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.CanonicalPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter

/-! # Canonical Alternation -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation

noncomputable section

/-! Alternation of the actual canonical pairing over the original field.
The comparison with the reduced-base adapter retains the same Poincare
line, polarization map and scheme-valued pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PairingReflection

variable {k : Type} [Field k] {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (n : ℕ) (hn : 0 < n)

theorem reducedPairing_eq_field : AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn =
    AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn := rfl

theorem fieldCanonicalPairing_alternating (T : Over (Spec (.of k)))
    (x : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  apply PairingReflection.torsion_alternating_of_field_pullback s (Grp.mk A.scheme) n
    (AbelianScheme.IsogenyQuotient.Field.PolarizationAdapter.Construction.fieldNativePolarizationPairing A D pol n hn) _ T x
  intro U y
  rw [← AbelianScheme.IsogenyQuotient.Field.CanonicalPairingBaseChange.Construction.fieldNativePolarizationPairing_baseChange D pol n hn s]
  exact AbelianScheme.IsogenyQuotient.Field.PolarizationAlternating.Construction.fieldNativePolarizationPairing_alternating (D.pullback s) (pol.pullback s) n hn U y

theorem reducedFieldPairing_alternating (T : Over (Spec (.of k)))
    (x : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) :
    (AbelianScheme.IsogenyQuotient.ReducedPolarizationAdapter.Construction.reducedBaseNativePolarizationPairing A D pol n hn).pairValue x x = 1 := by
  rw [reducedPairing_eq_field]
  exact fieldCanonicalPairing_alternating A D pol n hn T x

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CanonicalAlternation
