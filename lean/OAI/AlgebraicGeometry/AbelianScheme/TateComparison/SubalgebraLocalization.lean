import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SpanDenominatorClearing
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Subalgebra Localization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SubalgebraLocalization

noncomputable section

/-! A subalgebra whose elements clear all central denominators presents
the ambient algebra as an actual localization. -/

theorem subalgebra_awayLocalization {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (W : Subalgebra R A) (z : W) (hz : IsUnit (z : A))
    (hclear : ∀ x : A, ∃ n : ℕ, (z : A) ^ n * x ∈ W) : IsLocalization.Away z A where
  map_units y := by
    obtain ⟨n, hn⟩ := y.property
    change IsUnit (y.val : A)
    rw [← hn]
    exact hz.pow n
  surj x := by
    obtain ⟨n, hn⟩ := hclear x
    refine ⟨(⟨(z : A) ^ n * x, hn⟩, ⟨z ^ n, ⟨n, rfl⟩⟩), ?_⟩
    exact mul_comm x ((z : A) ^ n)
  exists_of_eq := by
    intro x y h
    have he : x = y := Subtype.ext h
    subst y
    exact ⟨1, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SubalgebraLocalization
