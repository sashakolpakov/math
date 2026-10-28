import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Differential
import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RightDifferential

/-! # Association -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Association

noncomputable section

/-! Canonical regrouping of a first-quadrant triple total. Its map
preserves each actual triple injection, and the three signed
differentials coincide term by term. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasFiniteCoproducts A]

local instance total (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance complexTotal (K : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ)) :
    K.HasTotal (.up ℕ) := AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

variable (T : HomologicalComplex₂ (CochainComplex A ℕ) (.up ℕ) (.up ℕ))
open OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Components
attribute [local irreducible] Components.leftInjection Components.rightInjection

theorem differential (N : ℕ) :
    Components.component T N ≫ (Components.left T).d N (N + 1) = (Components.right T).d N (N + 1) ≫ Components.component T (N + 1) := by
  apply Components.right_hom_ext T N
  intro r i j hN
  erw [← Category.assoc, Components.rightInjection_component, Differential.left_d,
    ← Category.assoc, RightDifferential.right_d, add_comp, add_comp,
    Linear.units_smul_comp, Linear.units_smul_comp, Category.assoc,
    Components.rightInjection_component, Category.assoc, Components.rightInjection_component,
    Category.assoc, Components.rightInjection_component]

def map : Components.right T ⟶ Components.left T where
  f := Components.component T
  comm' N M h := by
    obtain rfl : M = N + 1 := h.symm
    exact differential T N

@[reassoc]
theorem injection (r i j N : ℕ) (h : r + i + j = N) :
    Components.rightInjection T r i j N h ≫ (map T).f N = Components.leftInjection T r i j N h :=
  Components.rightInjection_component T r i j N h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.Association
