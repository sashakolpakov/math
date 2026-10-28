import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Symmetry

/-! # Symmetry -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Symmetry.Constructions

noncomputable section

/-! The actual Serre intersection coefficient is symmetric in its two
reduced supports, by symmetry of the native categorical Tor modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem localTorLength_comm (X : Scheme) (A B : IrreducibleCloseds X)
    (x : X) (hxA : x ∈ (A : Set X)) (hxB : x ∈ (B : Set X)) (i : ℕ) :
    IntersectionGeometry.localTorLength X A B x hxA hxB i = IntersectionGeometry.localTorLength X B A x hxB hxA i :=
  TorAlgebra.Symmetry.Tor.length_comm _ _ _ i

theorem intersectionMultiplicity_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier) :
    IntersectionGeometry.intersectionMultiplicity X A B C = IntersectionGeometry.intersectionMultiplicity X B A C := by
  classical
  by_cases h : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier) ∩ (B : Set X.carrier)
  · rw [IntersectionGeometry.intersectionMultiplicity, dite_eq_left h, IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨h.2, h.1⟩]
    apply Finset.sum_congr rfl
    intro i _
    rw [localTorLength_comm]
  · have hn : IntersectionGeometry.supportPoint C ∉ (B : Set X.carrier) ∩ (A : Set X.carrier) := fun hb => h ⟨hb.2, hb.1⟩
    rw [IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, IntersectionGeometry.intersectionMultiplicity, dite_eq_right hn]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Symmetry.Constructions
