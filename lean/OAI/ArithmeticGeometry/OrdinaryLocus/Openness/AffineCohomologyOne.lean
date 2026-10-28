import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveGlobalExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Affine Cohomology One -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCohomologyOne.Construction

noncomputable section

/-! Vanishing of ordinary sheaf cohomology in degree one on affine schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Abelian

universe u

theorem projective_uliftInt : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) where
  factors q b hb := by
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective b).mp hb
      (q (ULift.up 1))
    refine ⟨AddCommGrpCat.ofHom (uliftZMultiplesHom _ x), ?_⟩
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    rintro ⟨n⟩
    change b (uliftZMultiplesHom _ x (ULift.up n)) = q (ULift.up n)
    rw [uliftZMultiplesHom_apply_apply, map_zsmul, hx]
    change n • q.hom (ULift.up 1) = q.hom (ULift.up n)
    have hn : n • (ULift.up 1 : ULift.{u} ℤ) = ULift.up n := by
      apply ULift.ext
      change n • (1 : ℤ) = n
      simp
    exact (map_zsmul q.hom n (ULift.up 1)).symm.trans (congrArg q.hom hn)

variable (R : CommRingCat.{u})

abbrev affineConstantAbelian : AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R)) :=
  (constantSheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R))
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

def affineConstantAbelianAdjunction :
    constantSheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{u} ⊣
      AdditiveGlobalExact.Construction.additiveSheafEvaluation R ⊤ :=
  constantSheafAdj _ _ isTerminalTop

theorem affineConstantAbelianHom_lift
    (S : ShortComplex (AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))))
    (hS : S.ShortExact) (hF : AdditiveGlobalExact.Construction.HasExactAffineCechOne R S.X₁)
    (q : affineConstantAbelian R ⟶ S.X₃) :
    ∃ t : affineConstantAbelian R ⟶ S.X₂, t ≫ S.g = q := by
  let adj := affineConstantAbelianAdjunction R
  have : Projective (AddCommGrpCat.of (ULift.{u} ℤ)) := projective_uliftInt
  have : Epi ((AdditiveGlobalExact.Construction.additiveSheafEvaluation R ⊤).map S.g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (AdditiveGlobalExact.Construction.additive_globalSections_surjective_of_shortExact R S hS hF)
  let q' := (adj.homEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) S.X₃) q
  let t' := Projective.factorThru q' ((AdditiveGlobalExact.Construction.additiveSheafEvaluation R ⊤).map S.g)
  refine ⟨(adj.homEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) S.X₂).symm t', ?_⟩
  apply (adj.homEquiv (AddCommGrpCat.of (ULift.{u} ℤ)) S.X₃).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact Projective.factorThru_comp q' ((AdditiveGlobalExact.Construction.additiveSheafEvaluation R ⊤).map S.g)

local instance e40AffineAbEnoughInjectives :
    EnoughInjectives (AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))) :=
  AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives (TopCat.of (PrimeSpectrum R))

local instance e40AffineAbHasExt : HasExt.{u} (AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))) :=
  hasExt_of_enoughInjectives _

theorem affine_H_one_eq_zero
    (F : AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))) (hF : AdditiveGlobalExact.Construction.HasExactAffineCechOne R F)
    (e : CategoryTheory.Sheaf.H F 1) : e = 0 := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨q, hq⟩ := Ext.covariant_sequence_exact₁ (affineConstantAbelian R) hS e
    (Ext.eq_zero_of_injective _) (rfl : 0 + 1 = 1)
  obtain ⟨q', rfl⟩ := (Ext.mk₀_bijective _ _).surjective q
  obtain ⟨t, ht⟩ := affineConstantAbelianHom_lift R S hS hF q'
  rw [← hq, ← ht, ← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]

theorem quasicoherent_affine_H_one_subsingleton (N : (Spec R).Modules) [N.IsQuasicoherent] :
    Subsingleton (CategoryTheory.Sheaf.H
      ((QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian R (TopCat.of (PrimeSpectrum R))).obj (modulesSpecToSheaf.obj N)) 1) := by
  apply subsingleton_of_forall_eq 0
  apply affine_H_one_eq_zero R
  apply AdditiveGlobalExact.Construction.hasExactAffineCechOne_of_localizing R
  exact (isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCohomologyOne.Construction
