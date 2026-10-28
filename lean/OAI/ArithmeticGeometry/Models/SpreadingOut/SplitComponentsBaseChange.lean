import OAI.ArithmeticGeometry.Models.SpreadingOut.FiniteOpenDescent

/-! # Split Components Base Change -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.SplitComponentsBaseChange.Construction

noncomputable section

/-! Finite split geometric component decompositions persist under base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem hasSplitGeometricComponents_of_isPullback
    {W X Y Z : Scheme.{u}} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) (H : Base.Construction.HasSplitGeometricComponents (Over.mk f)) :
    Base.Construction.HasSplitGeometricComponents (Over.mk q) := by
  obtain ⟨n, C, hdis, hcover, hconn⟩ := H
  refine ⟨n, fun i ↦ p ⁻¹ᵁ C i, ?_, p.iSup_preimage_eq_top hcover, ?_⟩
  · intro i j hij
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (hdis i j hij).eq_bot]
    rfl
  · intro i
    have : GeometricallyConnected ((C i).ι ≫ f) := hconn i
    exact MorphismProperty.of_isPullback
      ((isPullback_morphismRestrict p (C i)).paste_vert h) inferInstance

theorem hasSplitGeometricComponents_baseChange
    {S T : Scheme.{u}} (g : T ⟶ S) (X : Over S)
    (H : Base.Construction.HasSplitGeometricComponents X) :
    Base.Construction.HasSplitGeometricComponents ((Over.pullback g).obj X) :=
  hasSplitGeometricComponents_of_isPullback (IsPullback.of_hasPullback X.hom g) H

theorem hasSplitGeometricComponents_of_iso
    {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y)
    (H : Base.Construction.HasSplitGeometricComponents Y) : Base.Construction.HasSplitGeometricComponents X := by
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  have h : IsPullback e.hom.left X.hom Y.hom (𝟙 S) := by
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hasSplitGeometricComponents_of_isPullback h H

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.SplitComponentsBaseChange.Construction
