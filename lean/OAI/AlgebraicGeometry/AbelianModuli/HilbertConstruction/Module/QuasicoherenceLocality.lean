import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations

/-! # Quasicoherence Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality

noncomputable section

/-! Quasicoherence can be checked on restrictions to actual affine open subschemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_over_quasicoherent_of_affine_restriction
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) [IsAffine U.toScheme]
    [(M.restrict U.ι).IsQuasicoherent] : (M.over U).IsQuasicoherent := by
  let N := M.restrict U.ι
  let P : N.Presentation := Affine.ModulePresentations.quasicoherentAffinePresentation N
  let : (overEquiv U).inverse.IsEquivalence := inferInstance
  let hPres : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse := inferInstance
  let Q : ((overEquiv U).inverse.obj N).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (overEquiv U).inverse hPres (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : M.over U ≅ (overEquiv U).inverse.obj N :=
    (overEquiv U).unitIso.app (M.over U) ≪≫
      (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)
  let Q' : (M.over U).Presentation :=
    @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.inv e.isIso_inv Q
  exact Q'.isQuasicoherent

theorem module_quasicoherent_of_affine_restrictions
    {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ U : X.affineOpens, (M.restrict U.1.ι).IsQuasicoherent) : M.IsQuasicoherent := by
  have hlocal (U : X.affineOpens) : (M.over U.1).IsQuasicoherent := by
    have : IsAffine U.1.toScheme := U.2
    have := hM U
    exact module_over_quasicoherent_of_affine_restriction M U.1
  have hcover : (Opens.grothendieckTopology X).CoversTop (fun U : X.affineOpens => U.1) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _ M _
    (fun U : X.affineOpens => U.1) hcover hlocal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality
