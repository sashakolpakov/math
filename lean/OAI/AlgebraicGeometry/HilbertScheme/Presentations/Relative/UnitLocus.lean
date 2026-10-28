import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OpenUnitLocus
import Mathlib.AlgebraicGeometry.Limits

/-! # Unit Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitLocus

noncomputable section

/-! The principal-open unit locus with its universal property over a base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S)

theorem relative_unit_locus (s : Γ(M.left, ⊤)) :
    ∃ (U : Over S) (j : U ⟶ M), IsOpenImmersion j.left ∧
      ∀ (T : Over S) (x : T ⟶ M), IsUnit (x.left.appTop s) ↔ ∃! y : T ⟶ U, y ≫ j = x := by
  let V : M.left.Opens := M.left.basicOpen s
  let U : Over S := Over.mk (V.ι ≫ M.hom)
  let j : U ⟶ M := Over.homMk V.ι rfl
  have hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V.ι)
  let := hj
  have : Mono j := Over.mono_of_mono_left j
  have hs : IsUnit (j.left.appTop s) := by
    apply (OpenUnitLocus.isUnit_appTop_iff_range_subset j.left s).mpr
    change Set.range V.ι ⊆ (V : Set M.left)
    rw [Scheme.Opens.range_ι]
  refine ⟨U, j, hj, ?_⟩
  intro T x
  constructor
  · intro hx
    have hrange : Set.range x.left ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      exact (OpenUnitLocus.isUnit_appTop_iff_range_subset x.left s).mp hx
    let y := IsOpenImmersion.lift V.ι x.left hrange
    have hy : y ≫ V.ι = x.left := IsOpenImmersion.lift_fac V.ι x.left hrange
    let y' : T ⟶ U := Over.homMk y (by
      change y ≫ (V.ι ≫ M.hom) = T.hom
      rw [← Category.assoc, hy, x.w])
    refine ⟨y', ?_, ?_⟩
    · apply Over.OverMorphism.ext
      exact hy
    · intro z hz
      apply (cancel_mono j).mp
      exact hz.trans (by apply Over.OverMorphism.ext; exact hy.symm)
  · rintro ⟨y, hy, _⟩
    rw [← hy]
    exact hs.map y.left.appTop.hom

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.UnitLocus
