import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Numerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PresentationSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ExactSequenceFinrank

/-! # Hilbert Additivity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertAdditivity

noncomputable section

/-! Canonical Hilbert polynomials are additive for actual short exact
sequences of coherent projective modules. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ}

theorem projectiveHilbertFunction_eventually_add_of_shortExact
    (T : ShortComplex (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
    (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    [T.X₁.IsFiniteType] [T.X₂.IsFiniteType] [T.X₃.IsFiniteType]
    (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      Projective.Numerics.Construction.projectiveHilbertFunction T.X₂ j n =
        Projective.Numerics.Construction.projectiveHilbertFunction T.X₁ j n + Projective.Numerics.Construction.projectiveHilbertFunction T.X₃ j n := by
  have : Epi T.g := hT.epi_g
  obtain ⟨b, hb⟩ := SheafCohomology.Projective.PresentationSections.MvPolynomial.finiteType_exact_eventually_projectiveTwist_sections T hT.exact j
  refine ⟨b, fun n hn => ?_⟩
  let F := (SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := K) j n).functor
  let G := SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) (σ := Fin (r + 1)))
  have hTF : (T.map F).ShortExact := hT.map_of_exact F
  have : Mono (F.map T.f) := hTF.mono_f
  have : (F.obj T.X₂).IsQuasicoherent :=
    SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent T.X₂ j n
  have : (F.obj T.X₂).IsFiniteType :=
    SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.moduleTensorCoordinateHyperplanePoleSheafPower_isFiniteType T.X₂ j n
  have : Module.Finite Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj T.X₂)) :=
    Projective.SectionFiniteness.Construction.projectiveGlobalSections_finite (F.obj T.X₂)
  let : Field Γ(Spec (CommRingCat.of K), ⊤) := Projective.Numerics.Construction.fieldSpec_sections_isField.toField
  let f := (G.map (F.map T.f)).hom
  let g := (G.map (F.map T.g)).hom
  have he : Function.Exact f g := (hb n hn).1
  have hf : Function.Injective f := SheafCohomology.Projective.GlobalSectionsMono.globalSections_injective_of_mono (F.map T.f)
  have hg : Function.Surjective g := (hb n hn).2
  have hd := SheafCohomology.Projective.ExactSequenceFinrank.finrank_eq_ranges_of_exact f g he
  rw [LinearMap.finrank_range_of_inj hf, LinearMap.range_eq_top.mpr hg, finrank_top] at hd
  change (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj T.X₂)) : ℚ) =
    (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj T.X₁)) : ℚ) +
      (Module.finrank Γ(Spec (CommRingCat.of K), ⊤) (G.obj (F.obj T.X₃)) : ℚ)
  exact_mod_cast hd

theorem projectiveHilbertPolynomial_add_of_shortExact
    (T : ShortComplex (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules)
    (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    [T.X₁.IsFiniteType] [T.X₂.IsFiniteType] [T.X₃.IsFiniteType]
    (j : Fin (r + 1)) :
    Projective.Numerics.Construction.projectiveHilbertPolynomial T.X₂ j =
      Projective.Numerics.Construction.projectiveHilbertPolynomial T.X₁ j + Projective.Numerics.Construction.projectiveHilbertPolynomial T.X₃ j := by
  obtain ⟨b, hb⟩ := projectiveHilbertFunction_eventually_add_of_shortExact T hT j
  unfold Projective.Numerics.Construction.projectiveHilbertPolynomial
  rw [← EventualPolynomial.Construction.eventualPolynomialValue_add]
  apply EventualPolynomial.Construction.eventualPolynomialValue_congr _ _ b hb

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertAdditivity
