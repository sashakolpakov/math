/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations

/-! # Quasicoherent Epimorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentEpimorphisms

noncomputable section

/-! Global sections on affine schemes preserve epimorphisms between quasicoherent modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

lemma quasicoherent_moduleSpecΓ_epi {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Epi (moduleSpecΓFunctor.map f) := by
  have : IsIso M.fromTildeΓ := inferInstance
  have : IsIso N.fromTildeΓ := inferInstance
  have hnat : tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := by
    have h := Scheme.Modules.fromTildeΓNatTrans.naturality f
    change tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f at h
    exact h
  have hright : Epi (M.fromTildeΓ ≫ f) :=
    epi_comp' (by infer_instance) (by infer_instance)
  have hcomp : Epi (tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ) :=
    hnat.symm ▸ hright
  have hmapped : Epi (tilde.map (moduleSpecΓFunctor.map f)) :=
    (epi_comp_iff_of_isIso _ N.fromTildeΓ).mp hcomp
  exact (tilde.functor R).epi_of_epi_map hmapped

theorem quasicoherent_spec_surjective_of_epi
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom :=
  (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map f)).mp
    (quasicoherent_moduleSpecΓ_epi f)

theorem quasicoherent_affine_surjective_of_epi [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective (f.val.app (op ⊤)).hom := by
  have hs : Function.Surjective (f.app (X.isoSpec.inv ''ᵁ ⊤)) :=
    quasicoherent_spec_surjective_of_epi
    ((restrictFunctor X.isoSpec.inv).map f)
  have ht : X.isoSpec.inv ''ᵁ ⊤ = ⊤ :=
    X.isoSpec.inv.image_top_eq_opensRange.trans X.isoSpec.inv.opensRange_of_isIso
  rw [ht] at hs
  exact hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentEpimorphisms
