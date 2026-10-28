import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.ComparisonIsomorphism
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Over Cartesian Family Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverCartesianFamilyIso

noncomputable section

/-! An actual relative family comparison constructs a cartesian
diagram of total schemes over the original scalar base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem over_cartesian_family_of_iso_with_projection {S : Scheme.{0}} {W T B : Over S}
    (a : W ⟶ T) (u : T ⟶ B) (Y : Over B.left)
    (e : Over.mk a.left ≅ (Over.pullback u.left).obj Y) :
    ∃ q : W ⟶ (Over.map B.hom).obj Y,
      q.left = e.hom.left ≫ pullback.fst Y.hom u.left ∧
      IsPullback a q u (Over.homMk Y.hom : (Over.map B.hom).obj Y ⟶ B) := by
  let q₀ := e.hom.left ≫ pullback.fst Y.hom u.left
  have hs : IsPullback a.left q₀ u.left Y.hom := by
    apply Cartesian.ComparisonIsomorphism.isPullback_of_isIso_comparison (IsPullback.of_hasPullback Y.hom u.left).flip e.hom.left
    · exact e.hom.w
    · rfl
  let Y₀ : Over S := (Over.map B.hom).obj Y
  let b : Y₀ ⟶ B := Over.homMk Y.hom rfl
  let q : W ⟶ Y₀ := Over.homMk q₀ (by
    change q₀ ≫ (Y.hom ≫ B.hom) = W.hom
    rw [← Category.assoc, ← hs.w, Category.assoc, u.w, a.w])
  have hsq : IsPullback a q u b := hs.of_map (Over.forget S) (Over.OverMorphism.ext hs.w)
  exact ⟨q, rfl, hsq⟩

theorem over_cartesian_family_of_iso {S : Scheme.{0}} {W T B : Over S}
    (a : W ⟶ T) (u : T ⟶ B) (Y : Over B.left)
    (e : Over.mk a.left ≅ (Over.pullback u.left).obj Y) :
    ∃ q : W ⟶ (Over.map B.hom).obj Y,
      IsPullback a q u (Over.homMk Y.hom : (Over.map B.hom).obj Y ⟶ B) := by
  obtain ⟨q, _, hc⟩ := over_cartesian_family_of_iso_with_projection a u Y e
  exact ⟨q, hc⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverCartesianFamilyIso
