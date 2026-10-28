import OAI.NumberTheory.ArithmeticGroups.Lattices.FractionalProjectionLift
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedBasis

/-! # Fractional Basis Lift -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FractionalBasisLift.Construction

noncomputable section

/-! A basis of a shortest-vector projected lattice lifts to an
integral basis with all new first-row coefficients bounded by one half. -/

open _root_.Module

theorem exists_fractional_basis_lift
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Λ : Submodule ℤ E) (v : Λ) (hv0 : v.val ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v.val‖ ≤ ‖x‖)
    {ι : Type*} (b : Basis ι ℤ (ProjectedLattice.Construction.projectedLattice Λ v.val)) :
    ∃ B : Basis (Unit ⊕ ι) ℤ Λ, ∃ c : ι → ℝ,
      B (Sum.inl ()) = v ∧ ∀ i, |c i| ≤ 1 / 2 ∧
        (B (Sum.inr i)).val = (b i).val.val + c i • v.val := by
  have hpre (i : ι) : ∃ y : Λ, ∃ c : ℝ, |c| ≤ 1 / 2 ∧
      y.val = (b i).val.val + c • v.val ∧ BoundedBasis.Construction.latticeProjection Λ v.val y = b i := by
    obtain ⟨x, hx, he⟩ := (b i).property
    change ProjectedLattice.Construction.perpendicularProjection v.val x = (b i).val at he
    obtain ⟨y, hy, c, hc, hform, hproj⟩ := FractionalProjectionLift.Construction.projection_fractional_lift Λ v.property hx
    refine ⟨⟨y, hy⟩, c, hc, ?_, Subtype.ext (hproj.trans he)⟩
    simpa only [he] using hform
  choose u c hc hform hu using hpre
  let : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  obtain ⟨B, hB0, hBi⟩ := BasisLift.Construction.basis_lift_cyclic_kernel (BoundedBasis.Construction.latticeProjection Λ v.val) v
    (fun h => hv0 (congrArg Subtype.val h)) (BoundedBasis.Construction.shortest_projection_kernel Λ v hv0 hmin) b u hu
  refine ⟨B, c, hB0, fun i => ?_⟩
  rw [hBi]
  exact ⟨hc i, hform i⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FractionalBasisLift.Construction
