import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Unitary Form Homeomorph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryFormHomeomorph.CM

noncomputable section

/-! Equality of the actual Hermitian matrices transports the unitary
group and its topology without changing matrix entries. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable {R I : Type*} [CommRing R] [StarRing R] [TopologicalSpace R]
  [Fintype I] [DecidableEq I] (H K : Matrix I I R) (h : H = K)

def equivalence : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H ≃ₜ* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU K := by
  subst K
  exact ContinuousMulEquiv.refl _

theorem matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H) : (equivalence H K h g).val.val = g.val.val := by
  subst K
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UnitaryFormHomeomorph.CM
