import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineEpiCover
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Affine Global Exact -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineGlobalExact.Construction

noncomputable section

/-! Global sections are right exact for affine sheaf sequences with quasicoherent kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : CommRingCat.{u})

abbrev affineSheafEvaluation (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R)) (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  sheafToPresheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R)) (ModuleCat R) ⋙
    (evaluation _ _).obj (op U)

variable (S : ShortComplex (CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R)) (ModuleCat.{u} R)))
    (hS : S.ShortExact)

include hS

theorem affine_shortExact_sections_exact (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    Function.Exact (S.f.hom.app (op U)) (S.g.hom.app (op U)) := by
  have : Mono S.f := hS.mono_f
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (hS.exact.map_of_mono_of_preservesKernel (affineSheafEvaluation R U)
      inferInstance inferInstance)

theorem affine_shortExact_sections_injective (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    Function.Injective (S.f.hom.app (op U)) := by
  have : Mono S.f := hS.mono_f
  exact (ModuleCat.mono_iff_injective ((affineSheafEvaluation R U).map S.f)).mp inferInstance

theorem affine_globalSections_surjective_of_shortExact
    (hF : IsLocalizing (R := R) S.X₁) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  classical
  have : Epi S.g := hS.epi_g
  intro s
  obtain ⟨q, f, hf, x, hx⟩ := @AffineEpiCover.Construction.affine_epi_finite_principal_lifts R S.X₂ S.X₃ S.g hS.epi_g s
  exact AffineLocalLifts.Construction.affine_global_lift_of_principal_local_lifts R S.X₁ S.X₂ S.X₃ S.f S.g hF
    (fun r ↦ affine_shortExact_sections_injective R S hS (PrimeSpectrum.basicOpen r))
    (fun r ↦ affine_shortExact_sections_exact R S hS (PrimeSpectrum.basicOpen r))
    f hf s x hx

theorem affine_globalSections_shortExact
    (hF : IsLocalizing (R := R) S.X₁) :
    (S.map (affineSheafEvaluation R ⊤)).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (affine_shortExact_sections_exact R S hS ⊤)
    (affine_shortExact_sections_injective R S hS ⊤)
    (affine_globalSections_surjective_of_shortExact R S hS hF)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineGlobalExact.Construction
