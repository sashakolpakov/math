import OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleHull
import OAI.NumberTheory.Quaternion.Arithmetic.HullCentralizer
import OAI.NumberTheory.Quaternion.Arithmetic.ConnectedAdjointIdeals

/-! # Almost Simple Lie Ideals -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleLieIdeals

noncomputable section

/-! A connected almost-simple algebraic group with semisimple Lie
algebra has no nonzero proper Lie ideal. A complementary ideal would
centralize the algebraic hull and hence the whole Lie algebra. -/

open scoped Classical
open Set

attribute [local instance] LieRing.ofAssociativeRing

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

local instance almostSimpleLieRationalTopology : TopologicalSpace G.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology G

theorem almostSimple_infinitesimal_ideal_eq_bot_or_top
    [PreconnectedSpace G.RationalPoints]
    [LieAlgebra.IsSemisimple k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)]
    (hsimple : ∀ N : Subgroup G.RationalPoints, N.Normal → IsClosed (N : Set G.RationalPoints) →
      IsConnected (N : Set G.RationalPoints) → N = ⊥ ∨ N = ⊤)
    (I : LieIdeal k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)) : I = ⊥ ∨ I = ⊤ := by
  by_cases hI0 : I = ⊥
  · exact Or.inl hI0
  right
  by_contra hI1
  have hIc : Iᶜ ≠ ⊥ := by simpa only [ne_eq, compl_eq_bot] using hI1
  obtain ⟨X, hXI, hX0⟩ : ∃ X ∈ I, X ≠ 0 := by
    have h : ¬ ∀ X, X ∈ I → X = 0 := fun h => hI0 ((LieSubmodule.eq_bot_iff I).mpr h)
    push Not at h
    exact h
  obtain ⟨Y, hYI, hY0⟩ : ∃ Y ∈ Iᶜ, Y ≠ 0 := by
    have h : ¬ ∀ Y, Y ∈ Iᶜ → Y = 0 := fun h => hIc ((LieSubmodule.eq_bot_iff Iᶜ).mpr h)
    push Not at h
    exact h
  let S := ConnectedAdjointIdeals.matrixIdealSubspace G I
  have hS : (S : Set (Matrix (Fin n) (Fin n) k)) ⊆ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
    rintro _ ⟨Z, _, rfl⟩
    exact Z.property
  have hconj : ∀ g : G.RationalPoints, ∀ A ∈ S,
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g.val⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S := by
    intro g A hA
    obtain ⟨Z, hZI, rfl⟩ := hA
    exact ⟨ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint G g Z, ConnectedAdjointIdeals.connected_adjoint_preserves_ideal G I g hZI,
      ArithmeticGroups.Lattices.ExponentialNormal.Construction.infinitesimalAdjoint_apply G g Z⟩
  have hSne : ∃ A ∈ (S : Set (Matrix (Fin n) (Fin n) k)), A ≠ 0 :=
    ⟨X.val, (ConnectedAdjointIdeals.mem_matrixIdealSubspace G I X).mpr hXI, fun h => hX0 (Subtype.ext h)⟩
  have htop := AlmostSimpleHull.differentialHull_eq_top_of_almostSimple G hsimple S hS hconj hSne
  have hIJ (Z T : ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) (hZ : Z ∈ I) (hT : T ∈ Iᶜ) : ⁅Z, T⁆ = 0 := by
    have hlie : ⁅Z, T⁆ ∈ I ⊓ Iᶜ :=
      ⟨lie_mem_left k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) I Z T hZ, (Iᶜ).lie_mem hT⟩
    rwa [inf_compl_eq_bot, LieSubmodule.mem_bot] at hlie
  have hSY : ∀ A ∈ S, A * Y.val = Y.val * A := by
    rintro A ⟨Z, hZI, rfl⟩
    exact sub_eq_zero.mp (congrArg Subtype.val (hIJ Z Y hZI hYI))
  have hGY : ∀ g : G.RationalPoints,
      (g.val : Matrix (Fin n) (Fin n) k) * Y.val = Y.val * (g.val : Matrix (Fin n) (Fin n) k) := by
    intro g
    apply HullCentralizer.differentialHull_commutes G S Y.val hSY g
    rw [htop]
    trivial
  have hcenter : Y ∈ LieAlgebra.center k (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) := by
    intro Z
    apply Subtype.ext
    exact sub_eq_zero.mpr (HullCentralizer.group_commutes_implies_infinitesimal_commutes G Y.val hGY Z.property)
  rw [LieAlgebra.center_eq_bot, LieSubmodule.mem_bot] at hcenter
  exact hY0 hcenter

end

end OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleLieIdeals
