import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.SectionPullback

/-! # Base Linear Section Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseLinearSectionPullback

noncomputable section

/-! Pullback of global module sections is linear over the actual base
scheme's section ring; base-preserving scheme isomorphisms give linear equivalences. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y S : Scheme.{u}}

def baseLinearSectionPullback (πX : X ⟶ S) (πY : Y ⟶ S) (f : X ⟶ Y) (hf : f ≫ πY = πX)
    (M : Y.Modules) :
    letI := Module.compHom Γ(M, ⊤) πY.appTop.hom
    letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, ⊤) πX.appTop.hom
    Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  letI := Module.compHom Γ(M, ⊤) πY.appTop.hom
  letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, ⊤) πX.appTop.hom
  refine
    { toFun := Global.SectionPullback.moduleGlobalSectionPullback f M
      map_add' := Global.SectionPullback.moduleGlobalSectionPullback_add f M
      map_smul' := ?_ }
  intro r s
  change Global.SectionPullback.moduleGlobalSectionPullback f M (πY.appTop r • s) = πX.appTop r • Global.SectionPullback.moduleGlobalSectionPullback f M s
  rw [Global.SectionPullback.moduleGlobalSectionPullback_smul, ← hf, Scheme.Hom.comp_appTop]
  rfl

def baseLinearSectionPullbackEquiv (πX : X ⟶ S) (πY : Y ⟶ S) (e : X ≅ Y) (he : e.hom ≫ πY = πX)
    (M : Y.Modules) :
    letI := Module.compHom Γ(M, ⊤) πY.appTop.hom
    letI := Module.compHom Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) πX.appTop.hom
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) := by
  letI := Module.compHom Γ(M, ⊤) πY.appTop.hom
  letI := Module.compHom Γ((Scheme.Modules.pullback e.hom).obj M, ⊤) πX.appTop.hom
  exact LinearEquiv.ofBijective (baseLinearSectionPullback πX πY e.hom he M)
    (Global.SectionPullback.moduleGlobalSectionPullback_bijective e M)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseLinearSectionPullback
