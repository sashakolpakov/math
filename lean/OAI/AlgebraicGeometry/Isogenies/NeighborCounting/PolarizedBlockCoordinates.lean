import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockCoordinates
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip

/-! # Polarized Block Coordinates -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockCoordinates

noncomputable section

/-! The Tate construction on a polarized source retains its original
integral action and its literal native block-point group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.BlockCoordinates OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip

variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {L : Type} [Field L] [CharZero L] {g N : ℕ} {δ : Fin g → ℕ}
  (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of L)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
  (τ : Gal(E/ℚ)) (k : Type) [Field k] [IsAlgClosed k] (f : Spec (.of k) ⟶ Spec (.of L))

abbrev polarizedFamily : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N (Spec (.of L)) :=
  AbelianScheme.TateComparison.PEL.PELFamilyData.ofPolarized PEL (AbelianScheme.TateComparison.PELAdapters.actionToEnd ρ)

def polarizedBlockPointsEquiv (n : ℕ) :=
  ActionRoundTrip.nativeBlockPointEquivOfEq (T := Over.mk f) (q ^ n)
    (p := (AbelianScheme.TateComparison.PELAdapters.actionFromEnd (polarizedFamily PEL ρ).action).map (j.projector iota hsplit n τ))
    (r := ρ.map (j.projector iota hsplit n τ))
    (AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap ρ (j.projector iota hsplit n τ))

variable
  (hcard : Nat.card (Additive (Over.mk f ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ 1)
    (ρ.map (j.projector iota hsplit 1 τ)))) = q ^ 3)

include hcard in
omit [IsGalois ℚ E] [CharZero L] [IsAlgClosed k] in
theorem polarizedFamily_geometric_card :
    Nat.card (Geometric.BlockCoordinates.originalGeometricBlock j iota hsplit (polarizedFamily PEL ρ) k f τ 1) = q ^ 3 :=
  (Nat.card_congr (polarizedBlockPointsEquiv j iota hsplit PEL ρ τ k f 1).toEquiv).trans hcard

def polarizedBlockCoordinates (n : ℕ) :
    Additive (Over.mk f ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))) ≃+
      (Fin 3 → ZMod (q ^ n)) :=
  (polarizedBlockPointsEquiv j iota hsplit PEL ρ τ k f n).symm.trans
    (Geometric.BlockCoordinates.geometricBlockCoordinates j iota hsplit (𝟙 (Spec (.of L))) (polarizedFamily PEL ρ) k f τ
      (polarizedFamily_geometric_card j iota hsplit PEL ρ τ k f hcard) n)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PolarizedBlockCoordinates
