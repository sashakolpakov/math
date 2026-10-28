import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.GeneratingPower
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Pointwise Generating Power -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Pointwise nonvanishing sections of positive powers give a finite generating family in one positive power, including for empty schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.exists_generating_power_of_pointwise
    {X : Scheme.{u}} [CompactSpace X] (L : Line.Bundles.LineBundle X)
    (h : ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : Line.Bundles.structureModule X ⟶ (L.tensorPower n).sheaf),
      x ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∃ (d : ℕ) (_ : 0 < d) (n : ℕ)
      (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ (L.tensorPower d).sheaf)),
      ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  obtain ⟨k, n, hn, s, hs⟩ := L.finite_powerSection_cover_of_pointwise h
  obtain ⟨d, hd, t, ht⟩ := L.common_generating_power_of_finite_cover n hn s hs
  refine ⟨d, hd, k, Fin.cases 0 t, fun x => ?_⟩
  obtain ⟨i, hi⟩ := ht x
  exact ⟨i.succ, hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
