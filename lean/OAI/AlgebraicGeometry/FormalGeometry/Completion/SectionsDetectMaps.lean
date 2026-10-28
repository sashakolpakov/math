import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionGeneration
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FixedNegativeQuotient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso

/-! # Sections Detect Maps -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionsDetectMaps

noncomputable section

/-! Global sections detect maps out of every sufficiently positive twist
of a coherent projective module. The proof uses its actual negative-twist quotient. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u v

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

theorem projectiveTwist_eventually_sectionsDetectMaps
    {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
    (M : (Proj (MvPolynomial.homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      GlobalSectionGeneration.Construction.SectionsDetectMaps
        ((SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M) := by
  classical
  obtain ⟨s, d, f, hf⟩ := SheafCohomology.Projective.FixedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient M j
  have : Epi f := hf
  refine ⟨Finset.univ.sup d, fun n hn => ?_⟩
  let F := (SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor
  let U := fun k : Fin s => SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)
  let V := fun k : Fin s => SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - d k)
  have hd (k : Fin s) : d k ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ k)).trans hn
  let e : (∐ V) ≅ F.obj (∐ U) :=
    (Sigma.mapIso fun k =>
      (SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE
        (R := R) j (d k) n (hd k)).symm) ≪≫
      (PreservesCoproduct.iso F U).symm
  have hV : GlobalSectionGeneration.Construction.SectionsDetectMaps (∐ V) :=
    GlobalSectionGeneration.Construction.SectionsDetectMaps.coproduct V fun k =>
      (Frame.SectionDetection.Construction.coordinatePositiveTwist_hasFrameSections (R := R) j (n - d k)).sectionsDetectMaps
  exact (hV.of_epi e.hom).of_epi (F.map f)

theorem projectiveTwist_eventually_globalSectionEvaluation_epi
    {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
    (M : (Proj (MvPolynomial.homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Epi (GlobalSectionGeneration.Construction.globalSectionEvaluation
        ((SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj M)) := by
  obtain ⟨b, hb⟩ := projectiveTwist_eventually_sectionsDetectMaps M j
  exact ⟨b, fun n hn => (hb n hn).evaluation_epi⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionsDetectMaps
