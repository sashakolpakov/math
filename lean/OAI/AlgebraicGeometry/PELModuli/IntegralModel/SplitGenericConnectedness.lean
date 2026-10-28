import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SplitComponents
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality

/-! # Split Generic Connectedness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A split arithmetic model of a geometrically connected smooth generic
fiber is geometrically connected over its entire arithmetic base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction

theorem SplitGenericConnectedness.geometricallyConnected_of_over_iso
    {B : Scheme} {X Y : Over B} (e : X ≅ Y) (hY : GeometricallyConnected Y.hom) :
    GeometricallyConnected X.hom := by
  have : IsIso e.hom.left := ((Over.forget B).mapIso e).isIso_hom
  have hs : IsPullback e.hom.left X.hom Y.hom (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  exact MorphismProperty.of_isPullback hs hY

theorem SplitGenericConnectedness.geometricallyConnected_of_connected_split
    {B : Scheme} (X : Over B) [ConnectedSpace X.left]
    (hX : ModelsHas.HasSplitGeometricComponents X) : GeometricallyConnected X.hom := by
  obtain ⟨n, C, hd, hc, hg⟩ := hX
  let x : X.left := Classical.choice inferInstance
  have hx : x ∈ ⨆ i, C i := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hcl : IsClopen (C i : Set X.left) :=
    ⟨ArithmeticGeometry.Models.SpreadingOut.SplitCoproducts.Construction.open_partition_isClosed C hd hc i, (C i).isOpen⟩
  have ht : C i = ⊤ := SetLike.coe_injective (hcl.eq_univ ⟨x, hi⟩)
  have h := hg i
  rw [ht] at h
  have hs : IsPullback X.left.topIso.inv X.hom
      (X.left.topIso.hom ≫ X.hom) (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact MorphismProperty.of_isPullback hs h

theorem Base.ArithmeticBaseExtension.split_model_geometricallyConnected
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) (X : Over B.base) [Smooth X.hom] [IsProper X.hom]
    [GeometricallyConnected ((Over.pullback B.generic).obj X).hom]
    (hX : ModelsHas.HasSplitGeometricComponents X) : GeometricallyConnected X.hom := by
  have : Smooth ((Over.pullback B.generic).obj X).hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd X.hom B.generic))
  have : IsProper ((Over.pullback B.generic).obj X).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd X.hom B.generic))
  have : ConnectedSpace ((Over.pullback B.generic).obj X).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback B.generic).obj X).hom
  have hi : IsIntegral ((Over.pullback B.generic).obj X).left :=
    ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral ((Over.pullback B.generic).obj X).hom
  have : IsIntegral ((Over.pullback (Spec.map (CommRingCat.ofHom B.toField))).obj X).left := hi
  have : IsIntegral X.left :=
    ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_model_integral_of_integral_generic B.toField B.toField_injective X
  exact SplitGenericConnectedness.geometricallyConnected_of_connected_split X hX

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
