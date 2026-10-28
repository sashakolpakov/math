import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.AffineKernels

/-! # Quasicoherent Kernels -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentKernels

noncomputable section

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

theorem restrict_preservesKernel {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (Scheme.Modules.restrictFunctor j) := by
  let D := parallelPair f 0
  let F := Scheme.Modules.restrictFunctor j
  change PreservesLimit D F
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  let G := SheafOfModules.forget X.ringCatSheaf
  have hall : ReflectsLimitsOfSize.{0, 0} G := fullyFaithful_reflectsLimits G
  have hshape : ReflectsLimitsOfShape WalkingParallelPair G := hall.reflectsLimitsOfShape
  have hlim : ReflectsLimit (D ⋙ F) G := hshape.reflectsLimit
  refine @isLimitOfReflects _ _ _ _ _ _ _ G _ ?_ hlim
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  let E := SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op (j ''ᵁ U.unop))
  let A := ModuleCat.restrictScalars (j.appIso U.unop).inv.hom
  have hE : PreservesLimit D E := SheafOfModules.evaluationPreservesLimit D _
  have hA : PreservesLimit (D ⋙ E) A := ModuleCat.preservesLimit_restrictScalars _ _
  change IsLimit (A.mapCone (E.mapCone c))
  exact @isLimitOfPreserves _ _ _ _ _ _ _ A _
    (@isLimitOfPreserves _ _ _ _ _ _ _ E _ hc hE) hA

theorem quasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  apply QuasicoherentCokernels.of_affine_restrictions (kernel f)
  intro U hU
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  let : PreservesLimit (parallelPair f 0) F := restrict_preservesKernel hU.fromSpec f
  have hq : (kernel (F.map f)).IsQuasicoherent :=
    AffineKernels.quasicoherent (F.map f)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    (PreservesKernel.iso F f).symm hq

theorem image {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (Abelian.image f).IsQuasicoherent := by
  let : (cokernel f).IsQuasicoherent := QuasicoherentCokernels.quasicoherent f
  exact quasicoherent (cokernel.π f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.QuasicoherentKernels
