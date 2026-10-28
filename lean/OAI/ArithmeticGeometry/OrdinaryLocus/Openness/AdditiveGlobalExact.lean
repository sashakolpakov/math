import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveEpiCover
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Additive Global Exact -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveGlobalExact.Construction

noncomputable section

/-! Exactness of global sections for abelian sheaf extensions with quasicoherent kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : CommRingCat.{u})

def HasExactAffineCechOne (F : AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R))) : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (f : ι → R),
    Ideal.span (Set.range f) = ⊤ →
      Function.Exact (AdditiveCech.Construction.additiveAffineD0 R F f) (AdditiveCech.Construction.additiveAffineD1 R F f)

theorem hasExactAffineCechOne_of_localizing
    (F : ModuleSheafInjectives.Construction.ModuleSheaves R (TopCat.of (PrimeSpectrum R))) (hF : IsLocalizing (R := R) F) :
    HasExactAffineCechOne R ((QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian R _).obj F) := by
  intro ι _ _ f hf
  exact QuasicoherentAdditiveCech.Construction.additiveAffine_exact_of_localizing R F hF f hf

abbrev additiveSheafEvaluation (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R)) ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (_root_.Opens.grothendieckTopology (PrimeSpectrum R)) AddCommGrpCat.{u} ⋙
    (evaluation _ _).obj (op U)

variable (S : ShortComplex (AbelianSheafInjectives.Construction.AbelianSheaves (TopCat.of (PrimeSpectrum R)))) (hS : S.ShortExact)

include hS

theorem additive_shortExact_sections_exact (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    Function.Exact (S.f.hom.app (op U)) (S.g.hom.app (op U)) := by
  have : Mono S.f := hS.mono_f
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (hS.exact.map_of_mono_of_preservesKernel (additiveSheafEvaluation R U)
      inferInstance inferInstance)

theorem additive_shortExact_sections_injective (U : TopologicalSpace.Opens (PrimeSpectrum R)) :
    Function.Injective (S.f.hom.app (op U)) := by
  have : Mono S.f := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective ((additiveSheafEvaluation R U).map S.f)).mp inferInstance

theorem additive_globalSections_surjective_of_shortExact (hF : HasExactAffineCechOne R S.X₁) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  classical
  intro s
  obtain ⟨q, f, hf, x, hx⟩ := @AdditiveEpiCover.Construction.additive_epi_finite_principal_lifts R S.X₂ S.X₃ S.g hS.epi_g s
  exact AdditiveLocalLifts.Construction.additiveAffine_global_lift R S.X₁ S.X₂ S.X₃ S.f S.g
    (fun r ↦ additive_shortExact_sections_injective R S hS (PrimeSpectrum.basicOpen r))
    (fun r ↦ additive_shortExact_sections_exact R S hS (PrimeSpectrum.basicOpen r))
    f (hF q f hf) hf s x hx

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdditiveGlobalExact.Construction
