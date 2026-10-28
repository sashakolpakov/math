import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Data.Finset.Lattice.Fold

/-! # Ring Sequence Colimit Elements -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceColimitElements

noncomputable section

/-! # Finite representatives and equality in a ring sequence colimit -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v

local instance forget_preservesSequences :
    PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{v}) :=
  preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget CommRingCat.{v})

variable (F : ℕ ⥤ CommRingCat.{v}) [HasColimit F]

theorem transition (i j : ℕ) (h : i ≤ j) (x : F.obj i) :
    (colimit.ι F j).hom ((F.map (homOfLE h)).hom x) = (colimit.ι F i).hom x :=
  congrArg (fun f : F.obj i ⟶ colimit F => f.hom x) (colimit.w F (homOfLE h))

theorem exists_rep (x : ↑(colimit F)) : ∃ i, ∃ y : F.obj i, (colimit.ι F i).hom y = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit F)) x

theorem exists_reps {ι : Type*} [Fintype ι] (x : ι → ↑(colimit F)) :
    ∃ i, ∃ y : ι → F.obj i, ∀ a, (colimit.ι F i).hom (y a) = x a := by
  classical
  choose n y hy using fun a => exists_rep F (x a)
  let N := Finset.univ.sup n
  refine ⟨N, fun a => (F.map (homOfLE (Finset.le_sup (Finset.mem_univ a)))).hom (y a), ?_⟩
  intro a
  exact (transition F (n a) N _ (y a)).trans (hy a)

theorem eq_iff (i : ℕ) (x y : F.obj i) :
    (colimit.ι F i).hom x = (colimit.ι F i).hom y ↔
      ∃ j, ∃ h : i ≤ j, (F.map (homOfLE h)).hom x = (F.map (homOfLE h)).hom y := by
  have he := Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit F)) x y
  constructor
  · intro h
    obtain ⟨j, f, hf⟩ := he.mp h
    exact ⟨j, leOfHom f, hf⟩
  · rintro ⟨j, h, hj⟩
    exact he.mpr ⟨j, homOfLE h, hj⟩

theorem inclusion_injective
    (hf : ∀ i j (h : i ≤ j), Function.Injective (F.map (homOfLE h)).hom) (i : ℕ) :
    Function.Injective (colimit.ι F i).hom := by
  intro x y h
  obtain ⟨j, hij, he⟩ := (eq_iff F i x y).mp h
  exact hf i j hij he

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.RingSequenceColimitElements
