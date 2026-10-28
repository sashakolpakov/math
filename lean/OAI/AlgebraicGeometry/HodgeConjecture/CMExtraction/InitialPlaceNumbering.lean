import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum

/-! # Initial Place Numbering -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialPlaceNumbering.Intrinsic

noncomputable section

/-! Number the active archimedean pair first before any test, level, or
prime is chosen. The place representatives are only permuted. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [NumberField.IsCMField E]

def initialPlacePermutation (places : HeckeCycles.GeometricSource.CM.Places E) : Equiv.Perm (Fin places.count) :=
  Equiv.swap ⟨0, Nat.zero_lt_of_lt places.distinguished.isLt⟩ places.distinguished

def activeFirstPlaces (places : HeckeCycles.GeometricSource.CM.Places E) : HeckeCycles.GeometricSource.CM.Places E where
  count := places.count
  representative i := places.representative (initialPlacePermutation E places i)
  distinguished := ⟨0, Nat.zero_lt_of_lt places.distinguished.isLt⟩
  identity := by
    dsimp [initialPlacePermutation]
    rw [Equiv.swap_apply_left]
    exact places.identity
  complete := by
    let e := (initialPlacePermutation E places).prodCongr (Equiv.refl Bool)
    exact places.complete.comp e.bijective

theorem activeFirstPlaces_representative (places : HeckeCycles.GeometricSource.CM.Places E) (i : Fin places.count) :
    (activeFirstPlaces E places).representative i =
      places.representative (initialPlacePermutation E places i) := rfl

theorem activeFirstPlaces_active (places : HeckeCycles.GeometricSource.CM.Places E) :
    (activeFirstPlaces E places).distinguished.val = 0 := rfl

theorem activeFirstPlaces_prescribed (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E)
    (d : Gal(E/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient E) :
    HeckeCycles.GeometricSource.CM.prescribed E B (activeFirstPlaces E places) d z w ↔ HeckeCycles.GeometricSource.CM.prescribed E B places d z w := by
  dsimp only [HeckeCycles.GeometricSource.CM.prescribed, activeFirstPlaces]
  let o : Fin places.count := ⟨0, Nat.zero_lt_of_lt places.distinguished.isLt⟩
  let e := initialPlacePermutation E places
  have he : ∀ i : Fin places.count, i = o ↔ e i = places.distinguished := by
    intro i
    have h0 : e o = places.distinguished := Equiv.swap_apply_left _ _
    rw [← h0]
    exact e.injective.eq_iff.symm
  constructor
  · intro h i
    have hi := h (e.symm i)
    change (if e.symm i = o then _ else _) at hi
    simpa only [← show e = initialPlacePermutation E places from rfl, he,
      e.apply_symm_apply] using hi
  · intro h i
    change if i = o then _ else _
    simp only [he]
    exact h (e i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialPlaceNumbering.Intrinsic
