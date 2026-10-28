import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.QuotientCover
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Principal Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.PrincipalCharts.Grassmannian

noncomputable section

/-!
Finite projective quotients admit coordinate bases on principal Zariski
neighborhoods. The selected coordinates are original global generators;
their localized linear-combination map is an actual isomorphism.
-/

open _root_.Module LocalizedModule

universe u

variable {R M ι ν : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]
variable [Fintype ι] [Fintype ν] [DecidableEq ι]

omit [DecidableEq ι] in
theorem generators_basis_atPrime (v : ν → M) (hv : Submodule.span R (Set.range v) = ⊤)
    (p : PrimeSpectrum R) (hr : Module.rankAtStalk M p = Fintype.card ι) :
    ∃ (a : ι → ν)
      (B : Basis ι (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M)),
      Function.Injective a ∧ ∀ i, B i = LocalizedModule.mkLinearMap p.asIdeal.primeCompl M (v (a i)) := by
  classical
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := LocalizedModule.AtPrime p.asIdeal M
  let l := LocalizedModule.mkLinearMap p.asIdeal.primeCompl M
  have : Module.Projective Rp Mp :=
    Module.Projective.of_equiv (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).symm
  have : Module.FinitePresentation Rp Mp := Module.finitePresentation_of_projective Rp Mp
  have hvp : Submodule.span Rp (Set.range (l ∘ v)) = ⊤ := by
    rw [Set.range_comp]
    exact span_eq_top_of_isLocalizedModule Rp p.asIdeal.primeCompl l hv
  obtain ⟨κ, a, B, hB⟩ := Module.exists_basis_of_span_of_flat (l ∘ v) hvp
  have ha : Function.Injective a := by
    intro i j hij
    apply B.injective
    rw [hB i, hB j, hij]
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let : Module.Free Rp Mp := Module.Free.of_basis B
  have hcard : Fintype.card κ = Fintype.card ι :=
    (Module.finrank_eq_card_basis B).symm.trans hr
  let e := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e.symm, B.reindex e, ha.comp e.symm.injective, ?_⟩
  intro i
  simpa only [Basis.reindex_apply, Function.comp_apply, l] using hB (e.symm i)

omit [Module.Finite R M] [Module.Projective R M] [Fintype ν] in
theorem selectedGenerators_surjective_atPrime (v : ν → M) (a : ι → ν)
    (p : PrimeSpectrum R)
    (B : Basis ι (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M))
    (hB : ∀ i, B i = LocalizedModule.mkLinearMap p.asIdeal.primeCompl M (v (a i))) :
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl
      (Fintype.linearCombination R (v ∘ a))) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← B.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ι → R) (Pi.single i 1), ?_⟩
  change LocalizedModule.map p.asIdeal.primeCompl (Fintype.linearCombination R (v ∘ a))
    (LocalizedModule.mk (Pi.single i 1) 1) = B i
  simp only [LocalizedModule.map_mk, Fintype.linearCombination_apply_single, one_smul]
  exact (hB i).symm

/-- Around every prime, a fixed subset of the generators is a basis of the
localized finite projective module. -/
theorem generators_principal_basis (v : ν → M) (hv : Submodule.span R (Set.range v) = ⊤)
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Fintype.card ι)
    (p : PrimeSpectrum R) :
    ∃ (r : R) (a : ι → ν), r ∉ p.asIdeal ∧ Function.Injective a ∧
      Function.Bijective (LocalizedModule.map (Submonoid.powers r)
        (Fintype.linearCombination R (v ∘ a))) := by
  have : Nontrivial R := p.nontrivial
  obtain ⟨a, B, ha, hB⟩ := generators_basis_atPrime v hv p (hr p)
  obtain ⟨r, hrp, hsur⟩ :=
    Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p.asIdeal
      (Fintype.linearCombination R (v ∘ a)) (selectedGenerators_surjective_atPrime v a p B hB)
  refine ⟨r, a, hrp, ha, Module.bijective_of_surjective_of_rankAtStalk_eq hsur ?_⟩
  intro m _
  rw [Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers r) (ι → R)),
    Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers r) M), hr]
  simp

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.PrincipalCharts.Grassmannian
