import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentEpimorphisms
import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-! # Zariski Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiExactness.ZariskiCohomology

noncomputable section

universe u
open _root_.CategoryTheory Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits

/-- The genuine Ext-based `H⁰` functor sends an epimorphism of
quasicoherent modules on `Spec R` to a surjective group homomorphism.

This is the checked cohomological consumer of
`moduleSpecGlobalSections_surjective_of_epi`. -/
theorem moduleSpecHZero_surjective_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi f] :
    Function.Surjective ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 0).map f) := by
  intro y
  obtain ⟨x, hx⟩ := QuasicoherentEpimorphisms.quasicoherent_spec_surjective_of_epi f
    (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections N y)
  let x' : Γ(M, ⊤) := x
  refine ⟨(Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M).symm x', ?_⟩
  apply (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections N).injective
  rw [← Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections_naturality]
  exact (congrArg (f.app ⊤) ((Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M).apply_symm_apply x')).trans hx

/-- The cokernel of a morphism between quasicoherent modules on an affine
spectrum is quasicoherent.

The proof transports the module cokernel through the left-adjoint tilde
functor, then compares the mapped cokernel with the scheme-module cokernel by
the counit isomorphisms `fromTildeΓ`. -/
theorem moduleSpec_isQuasicoherent_cokernel {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  let g := moduleSpecΓFunctor.map f
  have : IsIso M.fromTildeΓ := inferInstance
  have : IsIso N.fromTildeΓ := inferInstance
  let eM := asIso M.fromTildeΓ
  let eN := asIso N.fromTildeΓ
  have hnat :
      tilde.map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
        M.fromTildeΓ ≫ f := by
    exact Scheme.Modules.fromTildeΓNatTrans.naturality f
  let e₁ : tilde (cokernel g) ≅ cokernel (tilde.map g) := by
    exact PreservesCokernel.iso (tilde.functor R) g
  let e₂ : cokernel (tilde.map g) ≅ cokernel f :=
    cokernel.mapIso _ _ eM eN (by
      change tilde.map g ≫ N.fromTildeΓ = M.fromTildeΓ ≫ f
      simpa [g] using hnat)
  have hsource : (tilde (cokernel g)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (e₁ ≪≫ e₂) hsource

/-- The Ext-based `H⁰` map induced by a cokernel projection of
quasicoherent modules on an affine spectrum is surjective.

This is a checked cohomological consumer of
`moduleSpec_isQuasicoherent_cokernel`. -/
theorem moduleSpecHZero_surjective_cokernel_pi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective
      ((Zariski.Cohomology.ZariskiCohomology.zariskiFunctor (Spec R) 0).map (cokernel.π f)) := by
  let : (cokernel f).IsQuasicoherent :=
    moduleSpec_isQuasicoherent_cokernel f
  exact moduleSpecHZero_surjective_of_epi (cokernel.π f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiExactness.ZariskiCohomology
