import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountClosedStrata
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Finset.Powerset

/-! # Stratum Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.StratumNeighborhood.Construction

noncomputable section

/-! Actual principal affine opens isolating an entire maximal boundary stratum. -/

variable {R ι : Type*} [CommRing R]

/-- A finite family of ideals comaximal with `I` can simultaneously be
made unit on one principal open containing the entire closed locus of `I`. -/
theorem exists_principal_open_separating_ideals
    (I : Ideal R) (D : Finset ι) (J : ι → Ideal R)
    (hcoprime : ∀ d ∈ D, I ⊔ J d = ⊤) :
    ∃ f : R, 1 - f ∈ I ∧ (∀ d ∈ D, f ∈ J d) ∧
      (∀ q : Ideal R, q ≠ ⊤ → I ≤ q → f ∉ q) ∧
      ∀ d ∈ D, (J d).map (algebraMap R (Localization.Away f)) = ⊤ := by
  classical
  have hsup : I ⊔ ∏ d ∈ D, J d = ⊤ := Ideal.sup_prod_eq_top hcoprime
  have hone : (1 : R) ∈ I ⊔ ∏ d ∈ D, J d := by rw [hsup]; trivial
  obtain ⟨a, ha, f, hf, haf⟩ := Submodule.mem_sup.mp hone
  have hsub : 1 - f ∈ I := by rw [← haf, add_sub_cancel_right]; exact ha
  have hmem : ∀ d ∈ D, f ∈ J d := by
    intro d hd
    exact ((Ideal.prod_le_inf (s := D) (f := J)).trans (Finset.inf_le hd)) hf
  refine ⟨f, hsub, hmem, ?_, ?_⟩
  · intro q hq hIq hfq
    have h1 : (1 : R) ∈ q := by
      simpa only [sub_add_cancel] using q.add_mem (hIq hsub) hfq
    exact hq (Ideal.eq_top_of_isUnit_mem q h1 isUnit_one)
  · intro d hd
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (hmem d hd))
      (IsLocalization.Away.algebraMap_isUnit f)

variable {σ : Type*} [DecidableEq σ]

/-- The actual affine neighborhood contains every point of one maximal
boundary stratum and clears the ideals of every other maximal stratum. -/
theorem exists_maximal_boundary_stratum_neighborhood
    (w : σ → R) (B A : Finset σ) (F : Ideal R) (s : ℕ)
    (hbound : ∀ q : Ideal R, q.IsMaximal → F ≤ q →
      (CountReduction.Construction.activeBoundaryComponents w B q).card ≤ s)
    (hAB : A ⊆ B) (hAcard : A.card = s) :
    ∃ f : R, 1 - f ∈ CountClosedStrata.Construction.boundaryStratumIdeal w F A ∧
      (∀ q : Ideal R, q ≠ ⊤ → CountClosedStrata.Construction.boundaryStratumIdeal w F A ≤ q → f ∉ q) ∧
      ∀ D ⊆ B, D.card = s → D ≠ A →
        (CountClosedStrata.Construction.boundaryStratumIdeal w F D).map (algebraMap R (Localization.Away f)) = ⊤ := by
  classical
  let D := (B.powersetCard s).erase A
  have hcoprime : ∀ d ∈ D, CountClosedStrata.Construction.boundaryStratumIdeal w F A ⊔ CountClosedStrata.Construction.boundaryStratumIdeal w F d = ⊤ := by
    intro d hd
    obtain ⟨hdA, hdB⟩ := Finset.mem_erase.mp hd
    obtain ⟨hdB, hdcard⟩ := Finset.mem_powersetCard.mp hdB
    exact CountClosedStrata.Construction.maximal_boundary_stratum_ideals_comaximal w B A d F s hbound hAB hdB
      hAcard hdcard (Ne.symm hdA)
  obtain ⟨f, hf, _, hpoints, hunit⟩ := exists_principal_open_separating_ideals
    (CountClosedStrata.Construction.boundaryStratumIdeal w F A) D (CountClosedStrata.Construction.boundaryStratumIdeal w F) hcoprime
  refine ⟨f, hf, hpoints, ?_⟩
  intro d hdB hdcard hdA
  exact hunit d (Finset.mem_erase.mpr ⟨hdA, Finset.mem_powersetCard.mpr ⟨hdB, hdcard⟩⟩)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.StratumNeighborhood.Construction
