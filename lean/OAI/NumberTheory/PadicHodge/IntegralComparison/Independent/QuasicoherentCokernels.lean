import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentGluing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineCokernels
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators

/-! # Quasicoherent Cokernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentCokernels

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

def presentationSpec (R : CommRingCat.{u}) (M : (Spec R).Modules) [M.IsQuasicoherent] :
    M.Presentation := by
  let P := presentationTilde ((moduleSpecΓFunctor (R := R)).obj M) .univ (by simp)
    _ (Submodule.span_eq _)
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ M.fromTildeΓ
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M) P

def presentationOpen {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    [(M.restrict hU.fromSpec).IsQuasicoherent] : (M.restrict U.ι).Presentation := by
  let P := Scheme.Modules.presentationRestrict hU.isoSpec.hom
    (presentationSpec Γ(X, U) (M.restrict hU.fromSpec))
  let e := AffineOpen.ModuleGenerators.iso M U hU
  let he : IsIso e.hom := inferInstance
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom he P

theorem of_affine_restrictions {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ (U : X.Opens) (hU : IsAffineOpen U), (M.restrict hU.fromSpec).IsQuasicoherent) :
    M.IsQuasicoherent := by
  obtain ⟨κ, hκ, heq⟩ := Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (⊤ : X.Opens)
  apply QuasicoherentGluing.of_open_presentations M (fun U : κ => U.1)
    (by simpa only [IsOpenCover, sSup_eq_iSup'] using heq.symm)
  intro U
  have hU : IsAffineOpen (U.1 : X.Opens) := hκ U.2
  exact @presentationOpen X M U.1 hU (hM U.1 hU)

theorem quasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) : (cokernel f).IsQuasicoherent := by
  apply of_affine_restrictions (cokernel f)
  intro U hU
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction hU.fromSpec).leftAdjoint_preservesColimits
  have hq : (cokernel (F.map f)).IsQuasicoherent :=
    AffineCokernels.quasicoherent Γ(X, U) (F.map f)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso F f).symm hq

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentCokernels
