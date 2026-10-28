import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothDimensionCharts
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Dimension Uniqueness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DimensionUniqueness.DimensionSupport

noncomputable section

/-! Relative smooth dimension is uniquely determined on a nonempty
scheme, over arbitrary bases and in arbitrary characteristic. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem smooth_relative_dimension_unique
    {X S : Scheme} (f : X ⟶ S) [Nonempty X] (m n : ℕ)
    [SmoothOfRelativeDimension m f] [SmoothOfRelativeDimension n f] : m = n := by
  let x : X := Classical.arbitrary X
  let K := AlgebraicClosure (S.residueField (f x))
  let t : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (f x)) K)) ≫
      S.fromSpecResidueField (f x)
  let Y := pullback f t
  let p : Y ⟶ Spec (.of K) := pullback.snd f t
  have hdimension (d : ℕ) [SmoothOfRelativeDimension d f] : SmoothOfRelativeDimension d p := by
    have hstable := smoothOfRelativeDimension_isStableUnderBaseChange d
    exact hstable.of_isPullback (IsPullback.of_hasPullback f t) inferInstance
  have : SmoothOfRelativeDimension m p := hdimension m
  have : SmoothOfRelativeDimension n p := hdimension n
  have : Smooth p := SmoothOfRelativeDimension.smooth m p
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  have : Nonempty Y := by
    have hx : f x = t (IsLocalRing.closedPoint K) :=
      (S.fromSpecResidueField_apply (f x) _).symm
    obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := t)
      x (IsLocalRing.closedPoint K) hx
    exact ⟨z⟩
  obtain ⟨y, _, hy⟩ := nonempty_inter_closedPoints
    (X := Y) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hm := SmoothRelativeDimension.DimensionSupport.ringKrullDim_stalk_of_smoothOfRelativeDimension m p y hy
  have hn := SmoothRelativeDimension.DimensionSupport.ringKrullDim_stalk_of_smoothOfRelativeDimension n p y hy
  have he : (m : WithBot ℕ∞) = (n : WithBot ℕ∞) := hm.symm.trans hn
  exact_mod_cast he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.DimensionUniqueness.DimensionSupport
