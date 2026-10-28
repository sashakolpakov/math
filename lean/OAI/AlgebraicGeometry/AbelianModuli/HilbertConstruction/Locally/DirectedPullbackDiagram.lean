import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Directed Pullback Diagram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Locally.DirectedPullbackDiagram

noncomputable section

/-! A diagram containing a pullback for every span is locally directed and can be glued. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v w

theorem schemeDiagram_isLocallyDirected_of_pullbacks
    {J : Type v} [Category.{w} J] (F : J ⥤ Scheme.{u})
    (h : ∀ {i j k} (fi : i ⟶ k) (fj : j ⟶ k),
      ∃ (l : J) (fli : l ⟶ i) (flj : l ⟶ j),
        IsPullback (F.map fli) (F.map flj) (F.map fi) (F.map fj)) :
    (F ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro i j k fi fj xi xj hx
  obtain ⟨l, fli, flj, hl⟩ := h fi fj
  obtain ⟨x, hxi, hxj⟩ := Scheme.exists_preimage_of_isPullback hl xi xj hx
  exact ⟨l, fli, flj, x, hxi, hxj⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Locally.DirectedPullbackDiagram
