import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsSurjective
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Restriction Surjective -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.RestrictionSurjective

noncomputable section

/-! Restriction to a closed projective subscheme is surjective on sections
after sufficiently large twists. This is the actual structure-sheaf map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule
universe u

theorem closedImmersion_structure_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Epi (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have : F.Faithful := inferInstanceAs (SheafOfModules.toSheaf Y.ringCatSheaf).Faithful
  have : F.ReflectsEpimorphisms := Functor.reflectsEpimorphisms_of_faithful F
  apply F.epi_of_epi_map
  have hlocal : TopCat.Presheaf.IsLocallySurjective
      (F.map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t y hy
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
    let tV := ((Scheme.Modules.pushforward f).obj (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).presheaf.map
      (homOfLE hVU).op t
    obtain ⟨s, hs⟩ := f.app_surjective V hV tV
    exact ⟨V, hVU, ⟨s, hs⟩, hyV⟩
  let : CategoryTheory.Sheaf.IsLocallySurjective
      (F.map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := hlocal
  exact CategoryTheory.Sheaf.epi_of_isLocallySurjective _

attribute [local instance] MvPolynomial.gradedAlgebra

theorem eventually_projective_restriction_surjective {R : Type u} [CommRing R] [IsNoetherianRing R]
    {σ : Type} [Fintype σ] [LinearOrder σ] {X : Scheme.{u}}
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f] (j : σ) :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m → Function.Surjective
      (((SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j m).functor.map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).app ⊤) := by
  let Y := Proj (MvPolynomial.homogeneousSubmodule σ R)
  have : (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsQuasicoherent :=
    SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  have : (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsFinitePresentation :=
    SheafCohomology.Projective.InvertibleFinitePresentation.invertible_finitePresentation SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  have : (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y).IsFiniteType := inferInstance
  have : (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  have : ((Scheme.Modules.pushforward f).obj (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  let := closedImmersion_structure_epi f
  exact SheafCohomology.Projective.GlobalSectionsSurjective.MvPolynomial.finiteType_epi_eventually_projectiveTwist_sections_surjective
    (M := SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    (N := (Scheme.Modules.pushforward f).obj (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X))
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) j

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.RestrictionSurjective
