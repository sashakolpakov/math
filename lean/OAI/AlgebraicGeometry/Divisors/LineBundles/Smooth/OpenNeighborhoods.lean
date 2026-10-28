import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Open Neighborhoods -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.OpenNeighborhoods.BundleCycles

noncomputable section

/-! Smoothness is detected on actual open neighborhoods covering the source. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem smooth_of_open_neighborhoods {X Y : Scheme.{0}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ (U : Scheme.{0}) (i : U ⟶ X),
      IsOpenImmersion i ∧ x ∈ Set.range i ∧ Smooth (i ≫ f)) : Smooth f := by
  classical
  let : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  choose U i hi hx hf using h
  let C : X.OpenCover := Scheme.Cover.mkOfCovers X U i (fun x => ⟨x, hx x⟩) hi
  exact IsZariskiLocalAtSource.of_openCover (P := @Smooth) C hf

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.OpenNeighborhoods.BundleCycles
