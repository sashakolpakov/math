import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality

/-! # Coproducts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts

noncomputable section

/-! Actual coproducts of quasicoherent scheme modules are quasicoherent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem spec_quasicoherent_coproduct {R : CommRingCat.{u}} {ι : Type u}
    (M : ι → (Spec R).Modules) (hM : ∀ i, (M i).IsQuasicoherent) :
    (∐ M).IsQuasicoherent := by
  let A := fun i ↦ moduleSpecΓFunctor.obj (M i)
  let e (i) : (tilde.functor R).obj (A i) ≅ M i := by
    have hIso : IsIso (M i).fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ (M i)).mp (hM i)
    exact @asIso _ _ _ _ (M i).fromTildeΓ hIso
  let E : (∐ M) ≅ (tilde.functor R).obj (∐ A) :=
    Sigma.mapIso (fun i ↦ (e i).symm) ≪≫ (PreservesCoproduct.iso (tilde.functor R) A).symm
  have htilde : ((tilde.functor R).obj (∐ A)).IsQuasicoherent :=
    inferInstanceAs ((tilde (∐ A)).IsQuasicoherent)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso E.symm htilde

theorem affine_quasicoherent_coproduct {X : Scheme.{u}} [IsAffine X] {ι : Type u}
    (M : ι → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent) :
    (∐ M).IsQuasicoherent := by
  let F := restrictFunctor X.isoSpec.inv
  have hFM (i) : (F.obj (M i)).IsQuasicoherent := by
    have : (M i).IsQuasicoherent := hM i
    infer_instance
  have hsum : (∐ (F.obj ∘ M)).IsQuasicoherent := spec_quasicoherent_coproduct _ hFM
  have : (F.obj (∐ M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesCoproduct.iso F M).symm hsum
  have hres : ((F.obj (∐ M)).restrict X.isoSpec.hom).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((LineBundle.IsoImage.restrictFunctorInverseIso X.isoSpec).app (∐ M)) hres

theorem module_quasicoherent_coproduct {X : Scheme.{u}} {ι : Type u}
    (M : ι → X.Modules) (hM : ∀ i, (M i).IsQuasicoherent) :
    (∐ M).IsQuasicoherent := by
  apply Module.QuasicoherenceLocality.module_quasicoherent_of_affine_restrictions
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := restrictFunctor U.1.ι
  have hFM (i) : (F.obj (M i)).IsQuasicoherent := by
    have : (M i).IsQuasicoherent := hM i
    infer_instance
  have hsum : (∐ (F.obj ∘ M)).IsQuasicoherent := affine_quasicoherent_coproduct _ hFM
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (PreservesCoproduct.iso F M).symm hsum

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Coproducts
