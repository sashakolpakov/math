import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.GeometricKernelDescent

/-! # Line Geometric Ext -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineGeometricExt.Construction

noncomputable section

/-! Geometric points detect global functions, and hence line-bundle
endomorphisms, on reduced schemes of finite type over an algebraically
closed field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k : Type} [Field k] [IsAlgClosed k]

theorem global_section_eq_zero_of_rational
    (X : Over (Spec (.of k))) [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (r : Γ(X.left, ⊤))
    (hr : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ X, x.left.appTop r = 0) : r = 0 := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply eq_zero_of_basicOpen_eq_bot
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints
    (show ((X.left.basicOpen r : X.left.Opens) : Set X.left).Nonempty from ⟨z, hz⟩)
    (X.left.basicOpen r).isOpen.isLocallyClosed
  let x : Over.mk (𝟙 (Spec (.of k))) ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom w hwc) (pointOfClosedPoint_comp X.hom w hwc)
  have hx : (default : Spec (.of k)) ∈ x.left ⁻¹ᵁ X.left.basicOpen r := by
    change pointOfClosedPoint X.hom w hwc default ∈ X.left.basicOpen r
    exact (pointOfClosedPoint_apply X.hom w hwc (default : Spec (.of k))).symm ▸ hw
  rw [x.left.preimage_basicOpen_top, hr x, Scheme.basicOpen_zero] at hx
  exact hx

theorem global_section_ext_rational
    (X : Over (Spec (.of k))) [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (r s : Γ(X.left, ⊤))
    (h : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ X, x.left.appTop r = x.left.appTop s) : r = s := by
  apply sub_eq_zero.mp
  apply global_section_eq_zero_of_rational X (r - s)
  intro x
  rw [map_sub, h x, sub_self]

theorem lineBundle_end_ext_rational
    (X : Over (Spec (.of k))) [IsReduced X.left] [LocallyOfFiniteType X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (a b : End L.sheaf)
    (h : ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ X,
      (Scheme.Modules.pullback x.left).map a = (Scheme.Modules.pullback x.left).map b) : a = b := by
  apply (LineEndRigidity.Construction.lineBundleEndRingEquiv L).injective
  apply global_section_ext_rational X
  intro x
  rw [← LineEndRigidity.Construction.lineBundleEndRingEquiv_pullback, ← LineEndRigidity.Construction.lineBundleEndRingEquiv_pullback]
  exact congrArg (LineEndRigidity.Construction.lineBundleEndRingEquiv (L.pullback x.left)) (h x)

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineGeometricExt.Construction
