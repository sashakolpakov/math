import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel

/-! # Action Round Trip -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip

noncomputable section

/-! Passing an original integral action through the natural-endomorphism
interface recovers the same action, including every original scheme map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters

variable {R : Type} [CommRing R] {S : Scheme.{0}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem integralAction_ext {ρ σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A} (h : ρ.map = σ.map) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

theorem actionFromEnd_toEnd (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) :
    AbelianScheme.TateComparison.PELAdapters.actionFromEnd (AbelianScheme.TateComparison.PELAdapters.actionToEnd ρ) = ρ :=
  integralAction_ext (funext (AbelianScheme.TateComparison.PELAdapters.actionToEnd_schemeMap ρ))

def nativeBlockPointEquivOfEq {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A]
    (n : ℕ) {p r : A ⟶ A} [IsMonHom p] [IsMonHom r] (h : p = r) :
    Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) ≃+ Additive (T ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r) := by
  subst r
  exact AddEquiv.refl _

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActionRoundTrip
