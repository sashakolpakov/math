import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ManifoldSelection
import OAI.RepresentationTheory.Theta.Geometric.Rational.DomainSmooth
import OAI.RepresentationTheory.Theta.Geometric.Reference.ModuliOrbits
import OAI.RepresentationTheory.Theta.Geometric.Period.DomainTopology

/-! # Moduli Map Rigidity -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Global equality of original rational moduli maps has one fixed
original finite-level arithmetic comparison on the whole ball. -/

open scoped Classical _root_.Manifold ContDiff

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.rational_moduli_map_arithmetic_comparison
    (hg : D.pel.HasIntegralModelGeometry) (hc : D.HasFiniteCoordinates)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (g h : D.RationalSU)
    (he : ∀ x, D.referenceModuliMap hg (D.rationalPeriodPoint g x) =
      D.referenceModuliMap hg (D.rationalPeriodPoint h x)) :
    ∃ γ : D.RationalSU,
      D.rationalFinite γ ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup ∧
      ∀ x : D.domain, D.periodMap h x.val = D.periodMap γ (D.periodMap g x.val) := by
  let : Countable E := (Module.finBasis ℚ E).repr.injective.countable
  let : Countable (Matrix (Fin 3) (Fin 3) E) := inferInstanceAs (Countable (Fin 3 → Fin 3 → E))
  let : Countable (Matrix.SpecialLinearGroup (Fin 3) E) :=
    (show Function.Injective (fun z : Matrix.SpecialLinearGroup (Fin 3) E => z.val) from
      Subtype.val_injective).countable
  let : Countable D.RationalSU :=
    (show Function.Injective (fun z : D.RationalSU => z.val) from Subtype.val_injective).countable
  let Γ := {γ : D.RationalSU //
    D.rationalFinite γ ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup}
  let : Countable Γ := inferInstance
  let : Nonempty D.domain := ⟨D.domainOrigin hg⟩
  let : ContractibleSpace D.domain := D.domain_contractible hg
  let f : D.domain → LinearTheta.BallCoordinates := fun x => (D.rationalPeriodPoint h x).val
  let F : Γ → D.domain → LinearTheta.BallCoordinates := fun γ x =>
    (D.rationalPeriodPoint γ.val (D.rationalPeriodPoint g x)).val
  have hf : ContMDiff (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, LinearTheta.BallCoordinates)) 1 f :=
    (contMDiff_subtype_val.comp (D.rationalPeriodPoint_contMDiff h)).of_le (by simp)
  have hF (γ : Γ) : ContMDiff (𝓘(ℂ, LinearTheta.BallCoordinates)) (𝓘(ℂ, LinearTheta.BallCoordinates)) 1 (F γ) :=
    (contMDiff_subtype_val.comp
      ((D.rationalPeriodPoint_contMDiff γ.val).comp (D.rationalPeriodPoint_contMDiff g))).of_le (by simp)
  obtain ⟨γ, hγ⟩ := Holomorphic.ManifoldSelection.open_holomorphic_countable_selection D.domain
    (isPreconnected_iff_preconnectedSpace.mpr inferInstance) f F hf hF (fun x => by
      obtain ⟨γ, hγ, heq⟩ := (D.referenceModuliMap_orbits hg hc hgood hdegree
        (D.rationalPeriodPoint g x) (D.rationalPeriodPoint h x)).mp (he x)
      exact ⟨⟨γ, hγ⟩, heq⟩)
  exact ⟨γ.val, γ.property, fun x => congrFun hγ x⟩

end

end OAI.RepresentationTheory.Theta.Geometric
