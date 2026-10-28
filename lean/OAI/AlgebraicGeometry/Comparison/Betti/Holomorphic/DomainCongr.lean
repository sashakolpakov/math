import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions

/-! # Domain Congr -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DomainCongr

noncomputable section

/-! Equality of actual open domains gives the identity on holomorphic function values. -/

open _root_.TopologicalSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicFunctionDomainCongr {U V : Opens E} (h : U = V) :
    FunctionPure.holomorphicFunctions U ≃ₐ[ℂ] FunctionPure.holomorphicFunctions V where
  toFun := Restrictions.holomorphicFunctionRestrict h.ge
  invFun := Restrictions.holomorphicFunctionRestrict h.le
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

theorem holomorphicFunctionDomainCongr_apply {U V : Opens E} (h : U = V)
    (f : FunctionPure.holomorphicFunctions U) (x : V) :
    (holomorphicFunctionDomainCongr h f).val x = f.val ⟨x.val, h.ge x.property⟩ := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.DomainCongr
