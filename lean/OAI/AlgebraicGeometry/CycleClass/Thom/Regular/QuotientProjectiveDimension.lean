import Mathlib.RingTheory.Regular.ProjectiveDimension

/-! # Quotient Projective Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.QuotientProjectiveDimension.Constructions

noncomputable section

/-! The actual quotient by a local regular sequence has projective
dimension equal to its number of equations. -/

open _root_.CategoryTheory RingTheory.Sequence
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (rs : List R) (hr : IsWeaklyRegular R rs)
  (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)

include hr hm

theorem projectiveDimension_eq :
    projectiveDimension (ModuleCat.of R (R ⧸ Ideal.ofList rs)) = rs.length := by
  have h := ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
    (ModuleCat.of R R) rs hr hm
  have hi : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
    change Ideal.ofList rs * ⊤ = Ideal.ofList rs
    exact Ideal.mul_top _
  rw [hi, ModuleCat.projectiveDimension_eq_zero_of_projective (ModuleCat.of R R), zero_add] at h
  exact h

theorem bound : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.ofList rs)) rs.length :=
  (projectiveDimension_le_iff _ _).mp (projectiveDimension_eq R rs hr hm).le

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.QuotientProjectiveDimension.Constructions
