import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert

/-! # Restricted Away Homeomorph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayHomeomorph.CM

noncomputable section

/-! The two actual away-group models are isomorphic as topological groups. -/

open scoped Classical RestrictedProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedInsert.Approximation

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedPlaceProduct.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayComparison.CM

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]
  (K : ∀ i, Subgroup (G i)) (v : I)

def insert : CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v →* RestrictedPlaceProduct.CM.away K v :=
  (CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace K v).codRestrict (RestrictedPlaceProduct.CM.away K v) (CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace_same K v)

theorem forget_insert (g : CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v) : RestrictedAwayComparison.CM.forget K v (insert K v g) = g :=
  CMExtraction.RestrictedInsert.Approximation.restrictedForgetInsert K v g

theorem insert_forget (g : RestrictedPlaceProduct.CM.away K v) : insert K v (RestrictedAwayComparison.CM.forget K v g) = g := by
  apply Subtype.ext
  have h := CMExtraction.RestrictedInsert.Approximation.restrictedInsertForget K v g.val
  have hg : g.val v = 1 := g.property
  rw [hg, map_one, one_mul] at h
  exact h

def equivalence : RestrictedPlaceProduct.CM.away K v ≃* CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v where
  toFun := RestrictedAwayComparison.CM.forget K v
  invFun := insert K v
  left_inv := insert_forget K v
  right_inv := forget_insert K v
  map_mul' := (RestrictedAwayComparison.CM.forget K v).map_mul

variable [∀ i, TopologicalSpace (G i)]

theorem insert_continuous : Continuous (insert K v) :=
  (CMExtraction.RestrictedInsert.Approximation.restrictedInsertPlace_continuous K v).subtype_mk _

def homeomorphism : RestrictedPlaceProduct.CM.away K v ≃ₜ CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway K v where
  toEquiv := (equivalence K v).toEquiv
  continuous_toFun := RestrictedAwayComparison.CM.forget_continuous K v
  continuous_invFun := insert_continuous K v

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedAwayHomeomorph.CM
