import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionOverlapLifts

/-! # Factorization Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.FactorizationCriterion

noncomputable section

/-! Factorization through an actual closed subscheme is detected by the
vanishing of its pulled-back ideal sheaf, on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem closed_factorization_iff_comap_bot {X Y Z : Scheme.{u}}
    (i : X ⟶ Z) [IsClosedImmersion i] (f : Y ⟶ Z) :
    (∃! g : Y ⟶ X, g ≫ i = f) ↔ i.ker.comap f = ⊥ := by
  constructor
  · rintro ⟨g, rfl, _⟩
    rw [Scheme.IdealSheafData.comap_comp, ImmersionOverlapLifts.kernel_comap_self, Scheme.IdealSheafData.comap_bot]
  · intro h
    have hi : i.ker ≤ f.ker := by
      rw [← Scheme.IdealSheafData.map_bot f, Scheme.IdealSheafData.le_map_iff_comap_le, h]
    refine ⟨IsClosedImmersion.lift i f hi, IsClosedImmersion.lift_fac i f hi, ?_⟩
    intro g hg
    apply (cancel_mono i).mp
    exact hg.trans (IsClosedImmersion.lift_fac i f hi).symm

theorem over_closed_factorization_iff_comap_bot {S : Scheme.{u}} {X Y Z : Over S}
    (i : X ⟶ Z) [IsClosedImmersion i.left] (f : Y ⟶ Z) :
    (∃! g : Y ⟶ X, g ≫ i = f) ↔ i.left.ker.comap f.left = ⊥ := by
  constructor
  · rintro ⟨g, rfl, _⟩
    change i.left.ker.comap (g.left ≫ i.left) = ⊥
    rw [Scheme.IdealSheafData.comap_comp, ImmersionOverlapLifts.kernel_comap_self, Scheme.IdealSheafData.comap_bot]
  · intro h
    obtain ⟨g, hg, _⟩ := (closed_factorization_iff_comap_bot i.left f.left).mpr h
    have hw : g ≫ X.hom = Y.hom := by
      rw [← i.w, ← Category.assoc, hg]
      exact f.w
    let g' : Y ⟶ X := Over.homMk g hw
    have hg' : g' ≫ i = f := by
      ext
      exact hg
    have : Mono i := Over.mono_of_mono_left i
    exact ⟨g', hg', fun k hk => (cancel_mono i).mp (hk.trans hg'.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.FactorizationCriterion
