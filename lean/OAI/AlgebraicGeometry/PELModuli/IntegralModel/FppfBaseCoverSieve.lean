import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-! # Fppf Base Cover Sieve -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfBaseCoverSieve

noncomputable section

/-! Tests admitting a lift through a surjective fppf base cover form a
covering sieve. No finiteness or reducedness condition is imposed on tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S V : Scheme.{u}} (b : V ⟶ S)

def baseLiftSieve (T : Over S) : Sieve T where
  arrows Y _ := ∃ a : Y.left ⟶ V, a ≫ b = Y.hom
  downward_closed := by
    rintro Y Z f ⟨a, ha⟩ g
    exact ⟨g.left ≫ a, by rw [Category.assoc, ha]; exact g.w⟩

theorem baseLiftSieve_mem [Flat b] [Surjective b] [LocallyOfFinitePresentation b]
    (T : Over S) : baseLiftSieve b T ∈ (Scheme.fppfTopology.over S) T := by
  let p := pullback.fst T.hom b
  have hp : Sieve.generate (Presieve.singleton p) ∈ Scheme.fppfTopology T.left :=
    Precoverage.generate_mem_toGrothendieck p.singleton_mem_fppfPrecoverage
  apply (Scheme.fppfTopology.mem_over_iff _).mpr
  refine Scheme.fppfTopology.superset_covering ?_ hp
  apply (Sieve.generate_le_iff _ _).mpr
  intro Y f hf
  cases hf
  rw [Sieve.overEquiv_iff]
  exact ⟨pullback.snd T.hom b, pullback.condition.symm⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FppfBaseCoverSieve
