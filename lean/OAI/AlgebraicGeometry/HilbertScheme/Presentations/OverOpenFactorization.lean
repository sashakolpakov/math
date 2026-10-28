import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Over Open Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverOpenFactorization

noncomputable section

/-! The exact unique-factorization property of an open subscheme in
the category of schemes over a fixed base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S) (U : B.left.Opens)

def openOver : Over S := Over.mk (U.ι ≫ B.hom)

def openOverInclusion : openOver B U ⟶ B := Over.homMk U.ι rfl

instance openOverInclusion_isOpenImmersion : IsOpenImmersion (openOverInclusion B U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

instance openOverInclusion_mono : Mono (openOverInclusion B U) :=
  Over.mono_of_mono_left _

theorem range_subset_open_iff_unique_over_lift {T : Over S} (a : T ⟶ B) :
    Set.range a.left ⊆ (U : Set B.left) ↔
      ∃! b : T ⟶ openOver B U, b ≫ openOverInclusion B U = a := by
  constructor
  · intro h
    have hr : Set.range a.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      exact h
    let k := IsOpenImmersion.lift U.ι a.left hr
    have hk : k ≫ U.ι = a.left := IsOpenImmersion.lift_fac _ _ _
    let b : T ⟶ openOver B U := Over.homMk k (by
      change k ≫ U.ι ≫ B.hom = T.hom
      rw [← Category.assoc, hk, a.w])
    have hb : b ≫ openOverInclusion B U = a := by
      apply Over.OverMorphism.ext
      exact hk
    exact ⟨b, hb, fun c hc => (cancel_mono (openOverInclusion B U)).mp (hc.trans hb.symm)⟩
  · rintro ⟨b, hb, _⟩ y ⟨t, rfl⟩
    have he : b.left ≫ U.ι = a.left := congrArg (fun k => k.left) hb
    rw [← he]
    exact (b.left t).property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverOpenFactorization
