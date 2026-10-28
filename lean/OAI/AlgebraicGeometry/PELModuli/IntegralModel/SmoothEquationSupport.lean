import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackEquationProjection
import OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Smooth Equation Support -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationSupport

noncomputable section

/-! A smooth source makes the locus where two relative maps agree on
the entire fiber closed. It is defined by the actual scheme equalizer,
so it retains residue-field information, not merely equality of point images. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {X Y : Over S} [IsSeparated Y.hom] (l r : X ⟶ Y)

def smoothEquationSupport : Set S := (X.hom '' (Set.range (equalizer.ι l r).left)ᶜ)ᶜ

theorem smoothEquationSupport_closed [Smooth X.hom] : IsClosed (smoothEquationSupport l r) :=
  (X.hom.isOpenMap _ ((equalizer.ι l r).left.isClosedEmbedding.isClosed_range).isOpen_compl).isClosed_compl

omit [IsSeparated Y.hom] in
theorem equation_range_subset_support {T : Scheme.{0}} (t : T ⟶ S)
    (h : (Over.pullback t).map l = (Over.pullback t).map r) :
    Set.range t ⊆ smoothEquationSupport l r := by
  rintro _ ⟨z, rfl⟩ ⟨x, hx, hxt⟩
  have hp : x ∈ Set.range (pullback.fst X.hom t) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨z, hxt.symm⟩
  exact hx (PullbackEquationProjection.projection_range_subset_equalizer_of_equation l r t h hp)

omit [IsSeparated Y.hom] in
theorem support_projection_range {T : Scheme.{0}} (t : T ⟶ S)
    (h : Set.range t ⊆ smoothEquationSupport l r) :
    Set.range (pullback.fst X.hom t) ⊆ Set.range (equalizer.ι l r).left := by
  rw [Scheme.Pullback.range_fst]
  intro x hx
  by_contra hn
  obtain ⟨z, hz⟩ := hx
  exact h ⟨z, rfl⟩ ⟨x, hn, hz.symm⟩

theorem equation_of_support_range {T : Scheme.{0}} (t : T ⟶ S)
    [IsReduced (pullback X.hom t)] (h : Set.range t ⊆ smoothEquationSupport l r) :
    (Over.pullback t).map l = (Over.pullback t).map r := by
  let q := Albanese.Construction.ReducedFactor.factorThroughClosed (equalizer.ι l r).left (pullback.fst X.hom t)
    (support_projection_range l r t h)
  have hq : q ≫ (equalizer.ι l r).left = pullback.fst X.hom t :=
    Albanese.Construction.ReducedFactor.factorThroughClosed_comp _ _ _
  have he := congrArg (q ≫ ·) (congrArg Over.Hom.left (equalizer.condition l r))
  apply (PullbackEquationProjection.pullback_equation_iff_projection l r t).mpr
  simpa only [Over.comp_left, ← Category.assoc, hq] using he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationSupport
