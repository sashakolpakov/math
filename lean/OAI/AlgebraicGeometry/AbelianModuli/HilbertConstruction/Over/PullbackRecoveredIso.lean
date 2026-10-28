import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MapRealizationIso
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Pullback Recovered Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.PullbackRecoveredIso

noncomputable section

/-! An isomorphic Cartesian realization identifies the actual pullback of a morphism over a base as an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

theorem isIso_overPullback_map_of_recovered_iso
    {C : Type u} [Category.{v} C] [HasPullbacks C] {S T : C}
    {X Y : Over S} (f : X ⟶ Y) (c : T ⟶ S) {X' Y' : Over T}
    (qX : X'.left ⟶ X.left) (qY : Y'.left ⟶ Y.left)
    (hX : IsPullback qX X'.hom X.hom c) (hY : IsPullback qY Y'.hom Y.hom c)
    (f' : X' ⟶ Y') [IsIso f'] (hw : f'.left ≫ qY = qX ≫ f.left) :
    IsIso ((Over.pullback c).map f) := by
  have : IsIso f'.left := (Over.forget T).map_isIso f'
  have hk := HilbertConstruction.Pullback.MapRealizationIso.isIso_pullback_map_of_isIso_realization X.hom Y.hom c f.left f.w
    qX qY X'.hom Y'.hom hX hY f'.left hw f'.w
  have he : ((Over.pullback c).map f).left =
      pullback.map X.hom c Y.hom c f.left (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans f.w.symm) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left, pullback.map]
  have hleft : IsIso ((Over.pullback c).map f).left := (congrArg IsIso he).mpr hk
  have : IsIso ((Over.forget T).map ((Over.pullback c).map f)) := hleft
  exact isIso_of_reflects_iso ((Over.pullback c).map f) (Over.forget T)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.PullbackRecoveredIso
