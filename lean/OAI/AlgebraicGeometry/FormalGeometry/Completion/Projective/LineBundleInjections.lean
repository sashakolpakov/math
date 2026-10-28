import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionGeneration
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionMono

/-! # Line Bundle Injections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleInjections

noncomputable section

/-! Actual injections to and from sufficiently positive twists of any
line bundle on an integral closed projective scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

def lineBundleMapOfDualSection {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (N : X.Modules)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).sheaf ⊗ N) : L.sheaf ⟶ N :=
  (ρ_ L.sheaf).inv ≫
    (Iso.refl L.sheaf ⊗ᵢ Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.unitIso X).hom ≫
    (tensorLeft L.sheaf).map s ≫
    (α_ L.sheaf (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).sheaf N).inv ≫
    (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation L ⊗ᵢ Iso.refl N).hom ≫ (λ_ N).hom

theorem lineBundleMapOfDualSection_mono {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (N : X.Modules)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).sheaf ⊗ N) [Mono s] :
    Mono (lineBundleMapOfDualSection L N s) := by
  let E := Quotients.FiniteDescent.InvertibleProjectionTensor.Construction.InvertibleProjection.tensorEquivalence L.sheaf (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L).sheaf
    (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation L) (Quotients.FiniteDescent.MonoidalLine.Construction.MonoidalLineBundles.evaluation_swap L)
  have : Mono ((tensorLeft L.sheaf).map s) := E.functor.map_mono s
  unfold lineBundleMapOfDualSection
  infer_instance

theorem closedProjectiveLineBundle_eventually_injections
    {R : Type u} [CommRing R] {σ : Type} [Fintype σ]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : σ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ (a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf ⊗ (Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n))
        (c : L.sheaf ⟶ (Scheme.Modules.pullback f).obj
          (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)),
        Mono a ∧ Mono c := by
  obtain ⟨b, hb⟩ := SectionGeneration.Construction.closedProjectiveLineBundleTwist_eventually_hasFrameSections f L j
  obtain ⟨d, hd⟩ := SectionGeneration.Construction.closedProjectiveLineBundleTwist_eventually_hasFrameSections f (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L) j
  refine ⟨max b d, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hb n ((le_max_left _ _).trans hn) (genericPoint X)
  obtain ⟨s, hs⟩ := hd n ((le_max_right _ _).trans hn) (genericPoint X)
  have : Mono a := IntegralSectionMono.Construction.integral_section_mono_of_nonempty_nonvanishing a ⟨genericPoint X, ha⟩
  have : Mono s := IntegralSectionMono.Construction.integral_section_mono_of_nonempty_nonvanishing s ⟨genericPoint X, hs⟩
  exact ⟨a, lineBundleMapOfDualSection L _ s, inferInstance, lineBundleMapOfDualSection_mono L _ s⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleInjections
