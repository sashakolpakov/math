import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.CechConstants
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechEvaluation

/-! # Model Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.ModelGlobalFunctions.Construction

noncomputable section

/-! A finite free Cech model and residue exactness force literal
global functions to be precisely the functions on the local base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false in
theorem globalFunctions_iso_of_finite_cech_model
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
    (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) (ha : ⊤ ≤ σ ⁻¹ᵁ (∏ᶜ fun k : Fin 1 => U (a.val k)))
    {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U)
    [QuasiIsoAt φ 0] [Module.Finite R (D.X 0)] [Module.Finite R (D.X 1)]
    [Module.Free R (D.X 1)]
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map (IsLocalRing.ResidueField R) φ) 0]
    (hres : Function.Exact ((Relative.CechConstants.Construction.relativeCechConstants f U hU).lTensor (IsLocalRing.ResidueField R))
      (((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.lTensor (IsLocalRing.ResidueField R))) :
    IsIso f.appTop := by
  let E := FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hU
  let e := Relative.CechEvaluation.Construction.relativeCechEvaluation f σ hσ U a ha
  have hda : ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.comp (Relative.CechConstants.Construction.relativeCechConstants f U hU) = 0 := by
    apply LinearMap.ext
    intro r
    exact Relative.CechConstants.Construction.relativeCechConstants_cycle f U hU r
  have hs : Function.Surjective (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤) := by
    intro t
    let x := E t
    have he := CechConstants.Construction.finite_model_cycle_constants φ (Relative.CechConstants.Construction.relativeCechConstants f U hU) e
      (Relative.CechEvaluation.Construction.relativeCechEvaluation_constants f σ hσ U a ha hU) hda hres x.val x.property
    refine ⟨e x.val, ?_⟩
    apply E.injective
    apply Subtype.ext
    exact he.symm
  have hi : Function.Injective (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤) :=
    Function.LeftInverse.injective (fun r => Relative.CechEvaluation.Construction.sectionEvaluation_constants f σ hσ ⊤ (by simp) r)
  have : IsIso (CommRingCat.ofHom (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hi, hs⟩
  have he : CommRingCat.ofHom (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop := by
    simp [FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap, Scheme.Hom.appTop, Scheme.Hom.appLE]
  have : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) := he ▸ this
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv f.appTop

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.ModelGlobalFunctions.Construction
