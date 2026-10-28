import OAI.RepresentationTheory.Theta.Geometric.Torus.Hom

/-! # Linear Equiv -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.LinearEquiv

noncomputable section

/-! A complex-linear equivalence preserving the actual integral lattices
induces an additive biholomorphism of the original period quotients. -/

open scoped _root_.Manifold ContDiff

variable (Φ Ψ : Data.CM.ProjectivePeriodData)
    (e : Φ.space ≃ₗ[ℂ] Ψ.space)
    (he : ∀ v, e v ∈ Ψ.periodIntegerLattice ↔ v ∈ Φ.periodIntegerLattice)

def torusLinearEquiv : Φ.periodTorus ≃+ Ψ.periodTorus where
  toFun := Hom.torusLinearMap Φ Ψ e.toLinearMap (fun v hv => (he v).mpr hv)
  invFun := Hom.torusLinearMap Ψ Φ e.symm.toLinearMap (fun v hv =>
    (he (e.symm v)).mp ((congrArg (· ∈ Ψ.periodIntegerLattice) (e.apply_symm_apply v)).mpr hv))
  left_inv t := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact congrArg (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) (e.symm_apply_apply v)
  right_inv t := by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact congrArg (QuotientAddGroup.mk : Ψ.space → Ψ.periodTorus) (e.apply_symm_apply v)
  map_add' := (Hom.torusLinearMap Φ Ψ e.toLinearMap (fun v hv => (he v).mpr hv)).map_add

theorem torusLinearEquiv_mk (v : Φ.space) :
    torusLinearEquiv Φ Ψ e he (QuotientAddGroup.mk v) = QuotientAddGroup.mk (e v) := rfl

theorem torusLinearEquiv_symm_mk (v : Ψ.space) :
    (torusLinearEquiv Φ Ψ e he).symm (QuotientAddGroup.mk v) =
      QuotientAddGroup.mk (e.symm v) := rfl

def torusLinearDiffeomorph : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, Ψ.space)⟯ Ψ.periodTorus where
  toEquiv := (torusLinearEquiv Φ Ψ e he).toEquiv
  contMDiff_toFun := Hom.torusLinearMap_contMDiff Φ Ψ e.toLinearMap (fun v hv => (he v).mpr hv)
  contMDiff_invFun := Hom.torusLinearMap_contMDiff Ψ Φ e.symm.toLinearMap (fun v hv =>
    (he (e.symm v)).mp ((congrArg (· ∈ Ψ.periodIntegerLattice) (e.apply_symm_apply v)).mpr hv))

theorem torusLinearDiffeomorph_mk (v : Φ.space) :
    torusLinearDiffeomorph Φ Ψ e he (QuotientAddGroup.mk v) = QuotientAddGroup.mk (e v) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.LinearEquiv
