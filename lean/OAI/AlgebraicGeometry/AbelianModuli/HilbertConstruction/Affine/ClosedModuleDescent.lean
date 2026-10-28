import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.ModuleDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image

/-! # Closed Module Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ClosedModuleDescent

noncomputable section

/-! The actual pullback-pushforward unit is invertible for a quasicoherent
module annihilated by the ideal of an affine closed immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem affineModule_unit_isIso_of_kernel_annihilates
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (hf : Function.Surjective f.appTop.hom)
    (M : Y.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(Y, ⊤) Γ(M, ⊤)) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  let P := (pullback f).obj M
  have : P.IsQuasicoherent := QuasicoherentPullback.affine_pullback_quasicoherent f M
  have : ((pushforward f).obj P).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f P
  let a : M ⟶ (pushforward f).obj P := (pullbackPushforwardAdjunction f).unit.app M
  have hunit : IsIso ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
      ((SectionAdjunction.AffineSectionAdjunction.sections Y).obj M)) :=
    Quotient.ModuleDescent.quotientModule_unit_isIso f.appTop.hom hf _ h
  have he : IsIso ((SectionAdjunction.AffineSectionAdjunction.sections Y).map a ≫
      (SectionAdjunction.AffineSectionAdjunction.pushforwardIso f).hom.app P) := by
    rw [← GeometricSections.AffineGeometricSections.normalization f M, Adjunction.homEquiv_unit]
    infer_instance
  have ha : IsIso ((SectionAdjunction.AffineSectionAdjunction.sections Y).map a) :=
    IsIso.of_isIso_comp_right _ ((SectionAdjunction.AffineSectionAdjunction.pushforwardIso f).hom.app P)
  exact ModuleGlobalSectionsIsomorphism.affineModule_isIso_of_globalSections_isIso
    (M := M) (N := (pushforward f).obj P) a ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ClosedModuleDescent
