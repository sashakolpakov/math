import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure
import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitQuotient

/-! # Coset Homeomorphism -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CosetHomeomorphism.Construction

noncomputable section

/-! A topological group isomorphism induces a homeomorphism of coset
spaces, without requiring normality of the subgroups. -/

def cosetHomeomorphOfContinuousMulEquiv
    {H K : Type*} [Group H] [Group K] [TopologicalSpace H] [TopologicalSpace K]
    (e : H ≃ₜ* K) (Γ : Subgroup H) : (H ⧸ Γ) ≃ₜ (K ⧸ Γ.map e.toMonoidHom) where
  toFun := QuotientMeasure.Construction.cosetMap e.toMonoidHom Γ
  invFun := Quotient.map' e.symm fun x y hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    obtain ⟨g, hg, he⟩ := QuotientGroup.leftRel_apply.mp hxy
    have hh := congrArg e.symm he
    have hg' : e.symm (e.toMonoidHom g) = g := e.symm_apply_apply g
    have hh' : g = (e.symm x)⁻¹ * e.symm y := by
      rw [hg', map_mul, map_inv] at hh
      exact hh
    exact hh' ▸ hg
  left_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change QuotientGroup.mk (e.symm (e x)) = QuotientGroup.mk x
    rw [e.symm_apply_apply]
  right_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change QuotientGroup.mk (e (e.symm x)) = QuotientGroup.mk x
    rw [e.apply_symm_apply]
  continuous_toFun := QuotientMeasure.Construction.continuous_cosetMap e.toMonoidHom e.continuous Γ
  continuous_invFun := e.symm.continuous.quotient_map' _

@[simp] theorem cosetHomeomorphOfContinuousMulEquiv_mk
    {H K : Type*} [Group H] [Group K] [TopologicalSpace H] [TopologicalSpace K]
    (e : H ≃ₜ* K) (Γ : Subgroup H) (x : H) :
    cosetHomeomorphOfContinuousMulEquiv e Γ (QuotientGroup.mk x) = QuotientGroup.mk (e x) := rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CosetHomeomorphism.Construction
