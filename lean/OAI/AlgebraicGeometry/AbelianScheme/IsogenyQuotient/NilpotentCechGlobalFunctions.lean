import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechConstants
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CechEvaluation

/-! # Nilpotent Cech Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechGlobalFunctions.Construction

noncomputable section

/-! The nilpotent linear-algebra argument applies to literal global
functions through the native Cech zero-cycle equivalence. The residue
exactness and degree-one flatness are explicit at this assembly step. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u
variable {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal] (hI : IsNilpotent I)
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
  (a : SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.OrderedCechIndex ι 0) (ha : ⊤ ≤ σ ⁻¹ᵁ (∏ᶜ fun k : Fin 1 => U (a.val k)))
  [Module.Flat R ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).X 1)]
  (hres : Function.Exact ((Relative.CechConstants.Construction.relativeCechConstants f U hU).lTensor (R ⧸ I))
    (((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom.lTensor (R ⧸ I)))

include hI hσ ha hres in
set_option backward.isDefEq.respectTransparency false in
theorem globalFunctions_iso_of_nilpotent_cech : IsIso f.appTop := by
  let E := FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureGlobalSectionsEquiv f U hU
  let e := Relative.CechEvaluation.Construction.relativeCechEvaluation f σ hσ U a ha
  let d := ((FormalGeometry.Completion.RelativeCechZeroCycles.Construction.relativeStructureCechComplex f U).d 0 1).hom
  have hda : d.comp (Relative.CechConstants.Construction.relativeCechConstants f U hU) = 0 := by
    apply LinearMap.ext
    intro r
    exact Relative.CechConstants.Construction.relativeCechConstants_cycle f U hU r
  have hs : Function.Surjective (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤) := by
    intro t
    let x := E t
    have he := NilpotentCechConstants.Construction.nilpotent_split_augmentation_constants I hI (Relative.CechConstants.Construction.relativeCechConstants f U hU) e d
      (Relative.CechEvaluation.Construction.relativeCechEvaluation_constants f σ hσ U a ha hU) hda hres x.val x.property
    refine ⟨e x.val, ?_⟩
    apply E.injective
    apply Subtype.ext
    exact he.symm
  have hi : Function.Injective (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤) :=
    Function.LeftInverse.injective (fun r => Relative.CechEvaluation.Construction.sectionEvaluation_constants f σ hσ ⊤ (by simp) r)
  have : IsIso (CommRingCat.ofHom (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hi, hs⟩
  have he : CommRingCat.ofHom (FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap f ⊤) = (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop := by
    simp [FormalGeometry.Completion.Affine.InfinitesimalSections.Construction.baseOpenSectionsMap, Scheme.Hom.appTop, Scheme.Hom.appLE]
  have : IsIso ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) := he ▸ this
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of R)).inv f.appTop

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NilpotentCechGlobalFunctions.Construction
