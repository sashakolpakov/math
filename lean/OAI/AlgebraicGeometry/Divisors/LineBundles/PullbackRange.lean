import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Pullback Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PullbackRange.BundleCycles

/-! The actual scheme image on a cartesian chart is its set-theoretic preimage. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem range_of_isPullback {P X Y Z : Scheme} {a : P ⟶ X} {b : P ⟶ Y}
    {c : X ⟶ Z} {d : Y ⟶ Z} (h : IsPullback a b c d) :
    Set.range a = c ⁻¹' Set.range d := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, (congrArg (fun f : P ⟶ Z => f p) h.w).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, _⟩ := Scheme.exists_preimage_of_isPullback h x y hy.symm
    exact ⟨p, hp⟩

end OAI.AlgebraicGeometry.Divisors.LineBundles.PullbackRange.BundleCycles
