import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSheafInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Affine Ext One -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineExtOne.Construction

noncomputable section

/-! First cohomology of affine quasicoherent module sheaves, expressed as Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Abelian

universe u

variable (R : CommRingCat.{u})

abbrev affineConstantModule : ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R)) :=
  (constantSheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R))
    (ModuleCat.{u} R)).obj (ModuleCat.of R R)

def affineConstantModuleAdjunction :
    constantSheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R)) (ModuleCat.{u} R) ⊣
      AffineGlobalExact.Construction.affineSheafEvaluation R ⊤ :=
  constantSheafAdj _ _ isTerminalTop

theorem affineConstantModuleHom_lift
    (S : ShortComplex (ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))))
    (hS : S.ShortExact) (hF : IsLocalizing (R := R) S.X₁)
    (q : affineConstantModule R ⟶ S.X₃) :
    ∃ t : affineConstantModule R ⟶ S.X₂, t ≫ S.g = q := by
  let adj := affineConstantModuleAdjunction R
  have : Epi ((AffineGlobalExact.Construction.affineSheafEvaluation R ⊤).map S.g) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (AffineGlobalExact.Construction.affine_globalSections_surjective_of_shortExact R S hS hF)
  let q' := (adj.homEquiv (ModuleCat.of R R) S.X₃) q
  let t' := Projective.factorThru q' ((AffineGlobalExact.Construction.affineSheafEvaluation R ⊤).map S.g)
  refine ⟨(adj.homEquiv (ModuleCat.of R R) S.X₂).symm t', ?_⟩
  apply (adj.homEquiv (ModuleCat.of R R) S.X₃).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact Projective.factorThru_comp q' ((AffineGlobalExact.Construction.affineSheafEvaluation R ⊤).map S.g)

local instance e40AffineExtEnoughInjectives :
    EnoughInjectives (ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))) :=
  ModuleSheafInjectives.Construction.moduleSheaves_enoughInjectives R (TopCat.of (PrimeSpectrum R))

local instance e40AffineModuleHasExt :
    HasExt.{u} (ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))) :=
  hasExt_of_enoughInjectives _

theorem affine_ext_one_eq_zero
    (F : ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))) (hF : IsLocalizing (R := R) F)
    (e : Ext.{u} (affineConstantModule R) F 1) : e = 0 := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ (affineConstantModule R) hS e
    (Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  obtain ⟨q', rfl⟩ := (Ext.mk₀_bijective _ _).surjective q
  obtain ⟨t, ht⟩ := affineConstantModuleHom_lift R S hS hF q'
  rw [← hq, ← ht, ← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]

theorem affine_ext_one_subsingleton
    (F : ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))) (hF : IsLocalizing (R := R) F) :
    Subsingleton (Ext.{u} (affineConstantModule R) F 1) :=
  subsingleton_of_forall_eq 0 (affine_ext_one_eq_zero R F hF)

theorem quasicoherent_affine_ext_one_subsingleton (N : (Spec R).Modules) [N.IsQuasicoherent] :
    Subsingleton (Ext.{u} (affineConstantModule R) (modulesSpecToSheaf.obj N) 1) := by
  apply affine_ext_one_subsingleton R
  exact (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineExtOne.Construction
