import Mathlib.Topology.Algebra.ConstMulAction

/-! # Proper Action Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperActionTransport

/-! An equivariant homeomorphism and an injective map of acting
elements transfer finiteness of the translates meeting two compact sets. -/

theorem properlyDiscontinuous_of_equivariant_injection
    {G H X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [SMul G X] [SMul H Y]
    [ProperlyDiscontinuousSMul H Y] (f : G → H) (hf : Function.Injective f)
    (e : X ≃ₜ Y) (he : ∀ g x, e (g • x) = f g • e x) : ProperlyDiscontinuousSMul G X := by
  constructor
  intro K L hK hL
  have hfin : {h : H | (((h • ·) '' (e '' K)) ∩ (e '' L)).Nonempty}.Finite :=
    finite_disjoint_inter_image (hK.image e.continuous) (hL.image e.continuous)
  have hm : Set.MapsTo f {g : G | (((g • ·) '' K) ∩ L).Nonempty}
      {h : H | (((h • ·) '' (e '' K)) ∩ (e '' L)).Nonempty} := by
    rintro g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
    exact ⟨e (g • x), ⟨e x, ⟨x, hx, rfl⟩, (he g x).symm⟩, ⟨g • x, hgx, rfl⟩⟩
  exact Set.Finite.of_injOn hm hf.injOn hfin

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperActionTransport
