import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Diagonalizable
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Character Span -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.CharacterSpan

noncomputable section

/-! A full set of coordinate characters constructs a diagonalizable Hopf
presentation. The character-count hypothesis is a linear-algebra criterion;
its derivation from ordinary geometry is a separate step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A] [Module.Finite k A]

theorem finite_coordinateCharacters : Finite (GroupLike k A) :=
  (linearIndep_groupLikeVal (R := k) (A := A)).finite

theorem coordinateCharacters_span_of_card
    (hcard : Nat.card (GroupLike k A) = Module.finrank k A) :
    Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤ := by
  have : Finite (GroupLike k A) := finite_coordinateCharacters k A
  have : Fintype (GroupLike k A) := Fintype.ofFinite _
  apply (linearIndep_groupLikeVal (R := k) (A := A)).span_eq_top_of_card_eq_finrank'
  simpa only [Nat.card_eq_fintype_card] using hcard

def characterHopfEquivOfSpan
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤) :
    MonoidAlgebra k (GroupLike k A) ≃ₐc[k] A := by
  let q := MonoidAlgebra.liftGroupLikeBialgHom (R := k) (A := A)
  have hq : (q : MonoidAlgebra k (GroupLike k A) → A) =
      (Finsupp.linearCombination k GroupLike.val) ∘ MonoidAlgebra.coeff := by
    funext x
    simp only [q, MonoidAlgebra.liftGroupLikeBialgHom_apply,
      MonoidAlgebra.lift_apply, Finsupp.linearCombination_apply, Function.comp_apply]
    rfl
  apply BialgEquiv.ofBijective q
  rw [hq]
  exact ⟨linearIndep_groupLikeVal.finsuppLinearCombination_injective.comp
      MonoidAlgebra.coeffEquiv.injective,
    ((span_range_eq_top_iff_surjective_finsuppLinearCombination k
      (v := GroupLike.val)).mp hspan).comp MonoidAlgebra.coeffEquiv.surjective⟩

def characterHopfEquivOfCard
    (hcard : Nat.card (GroupLike k A) = Module.finrank k A) :
    MonoidAlgebra k (GroupLike k A) ≃ₐc[k] A :=
  characterHopfEquivOfSpan k A (coordinateCharacters_span_of_card k A hcard)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.CharacterSpan
