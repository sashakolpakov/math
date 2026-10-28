import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CenterAtlasGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBoundaryCenterExtension

/-! # Supported Center Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Extending a center supported inside an open neighborhood retains its constant boundary incidence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofSupportedOpen
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (j : V ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) {β : Type} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) (I.comap j) (fun l => (D l).comap j))
    (F : Finset β) (hF : ∀ i, B.divided i = F) (hsupport : (I.support : Set X) ⊆ Set.range j) :
    ∃ C : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D, ∀ i, C.divided i = F := by
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofCenterCharts f I D A F
  intro x hx
  obtain ⟨y, rfl⟩ := hsupport hx
  obtain ⟨i, p, hp⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec B.opens B.cover y
  let C := (Global.MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofAtlas B i).comp f I D j
  exact ⟨C, hF i, p, congrArg j hp⟩

theorem Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_order_supported_center
    {V X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (j : V ⟶ X) [IsOpenImmersion j]
    (J : X.IdealSheafData) (I : V.IdealSheafData) (n : ℕ)
    (hp : J.comap j ≤ I ^ (n + 1))
    (hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆ Set.range j)
    {β : Type} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)
    (B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) I (fun l => (D l).comap j))
    (F : Finset β) (hF : ∀ i, B.divided i = F) :
    ∃ C : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f (Global.OrderCenterExtension.Construction.openCenterExtension j I) D, ∀ i, C.divided i = F := by
  have hlocal : ∃ C : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (j ≫ f) ((Global.OrderCenterExtension.Construction.openCenterExtension j I).comap j)
      (fun l => (D l).comap j), ∀ i, C.divided i = F := by
    rw [Global.OrderCenterExtension.Construction.order_supported_center_extension_restrict f j J I n hp hcover]
    exact ⟨B, hF⟩
  obtain ⟨C, hC⟩ := hlocal
  apply Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.exists_uniform_ofSupportedOpen f j (Global.OrderCenterExtension.Construction.openCenterExtension j I) D A C F hC
  have hs := SupportedGlobalCenter.Construction.supported_center_kernel_support I.subschemeι j _
    (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed
    (Global.OrderCenterExtension.Construction.local_permissible_center_range_in_order_support f j J I n hp) hcover
  intro x hx
  obtain ⟨z, rfl⟩ := hs ▸ hx
  exact ⟨I.subschemeι z, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
