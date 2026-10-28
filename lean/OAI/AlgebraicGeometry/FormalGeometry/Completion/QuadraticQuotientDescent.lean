import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticKernelQuotient
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ReductionTransport
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.GroupTheory.Finiteness

/-! # Quadratic Quotient Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Arithmetic descent for a quadratic quotient, and finite generation
from a subgroup and its quotient. -/

universe u

variable {G : Type u} [AddCommGroup G]

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.quotient_finiteGenerated (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G)
    (D : ℕ) (hD : 0 < D) (hint : ∀ x : G, ∃ z : ℤ, (D : ℚ) * q.value x = z)
    (n : ℕ) (hn : 2 ≤ n)
    (hfinite : ∀ r : ℕ, Finite (G ⧸ (nsmulAddMonoidHom (n ^ r) : G →+ G).range)) :
    AddGroup.FG (G ⧸ q.zeroKernel) := by
  apply (q.quotientHeight D hD hint).finiteGenerated_of_finite_reductions n hn
  intro r
  have := hfinite r
  exact Completion.Finite.ReductionTransport.Construction.finite_nsmulQuotient_of_surjective (QuotientAddGroup.mk' q.zeroKernel)
    (QuotientAddGroup.mk'_surjective q.zeroKernel) (n ^ r)

theorem QuadraticQuotientDescent.Construction.addGroup_finiteGenerated_of_subgroup_quotient (S : AddSubgroup G)
    [AddGroup.FG S] [AddGroup.FG (G ⧸ S)] : AddGroup.FG G := by
  have : Module.Finite ℤ S := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have : Module.Finite ℤ (G ⧸ S) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let f := S.subtype.toIntLinearMap
  let g := (QuotientAddGroup.mk' S).toIntLinearMap
  have he : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, (QuotientAddGroup.eq_zero_iff (N := S) x).mp hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff (N := S) (x : G)).mpr x.property
  have : Module.Finite ℤ G := Module.Finite.of_exact he (QuotientAddGroup.mk'_surjective S)
  exact Module.Finite.iff_addGroup_fg.mp inferInstance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
