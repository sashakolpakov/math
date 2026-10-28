import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComposition

/-! # Relative Diagram -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeDiagram.RelativeDiagramSquare

noncomputable section

/-! A commuting square of original diagrams over a fixed base induces
a commuting square of their contravariant relative complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H H' K K' Q : C ⥤ IntegralComparison.BigCrystallineSite.Object p B J δ f)
  (π : H ⟶ Q) (π' : H' ⟶ Q) (ρ : K ⟶ Q) (ρ' : K' ⟶ Q)
  (a : H ⟶ H') (b : K ⟶ K') (c : H ⟶ K) (d : H' ⟶ K')
  (ha : a ≫ π' = π) (hb : b ≫ ρ' = ρ) (hc : c ≫ ρ = π) (hd : d ≫ ρ' = π')
  (h : a ≫ d = c ≫ b)

include h in
theorem square : IntegralComparison.Relative.DiagramComplexMap.map K K' Q ρ ρ' b hb ≫
      IntegralComparison.Relative.DiagramComplexMap.map H K Q π ρ c hc =
    IntegralComparison.Relative.DiagramComplexMap.map H' K' Q π' ρ' d hd ≫
      IntegralComparison.Relative.DiagramComplexMap.map H H' Q π π' a ha := by
  have h₁ := IntegralComparison.Relative.DiagramComposition.complex_comp H K K' Q π ρ ρ' c b hc hb
  have h₂ := IntegralComparison.Relative.DiagramComposition.complex_comp H H' K' Q π π' ρ' a d ha hd
  rw [← h₁, ← h₂]
  congr 1
  exact h.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeDiagram.RelativeDiagramSquare
