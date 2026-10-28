import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseLinearSectionPullback

/-! # Base Linear Section Iso -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseLinearSectionIso

noncomputable section

/-! An actual module-sheaf isomorphism identifies global sections
linearly over the base scheme's section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X S : Scheme.{u}}

def baseLinearSectionIso (π : X ⟶ S) {M N : X.Modules} (e : M ≅ N) :
    letI := Module.compHom Γ(M, ⊤) π.appTop.hom
    letI := Module.compHom Γ(N, ⊤) π.appTop.hom
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(N, ⊤) := by
  letI := Module.compHom Γ(M, ⊤) π.appTop.hom
  letI := Module.compHom Γ(N, ⊤) π.appTop.hom
  exact
    { toFun := e.hom.app ⊤
      invFun := e.inv.app ⊤
      left_inv := fun s => congrArg (fun f : M ⟶ M => f.app ⊤ s) e.hom_inv_id
      right_inv := fun s => congrArg (fun f : N ⟶ N => f.app ⊤ s) e.inv_hom_id
      map_add' := fun s t => (e.hom.app ⊤).hom.map_add s t
      map_smul' := fun r s => e.hom.app_smul (π.appTop r) s }

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseLinearSectionIso
