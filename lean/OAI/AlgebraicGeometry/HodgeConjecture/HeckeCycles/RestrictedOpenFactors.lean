import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Restricted Open Factors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOpenFactors.CM

noncomputable section

/-! An open subgroup of a restricted product contains every supported
integral local subgroup outside a finite set of places. -/

open scoped Classical RestrictedProduct _root_.Topology
open Filter OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  (K : ∀ i, Subgroup (G i))

def integralFamily : (∀ i, K i) →* RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K where
  toFun f := ⟨fun i => (f i).val, Eventually.of_forall (fun i => (f i).property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem integralFamily_continuous : Continuous (integralFamily K) :=
  (RestrictedProduct.continuous_inclusion (R := G) (A := fun i => (K i : Set (G i)))
    (show cofinite ≤ ⊤ from le_top)).comp
      (RestrictedProduct.homeoTop (R := G) (A := fun i => (K i : Set (G i)))).continuous

omit [∀ i, TopologicalSpace (G i)] in
theorem family_single (i : I) (g : K i) :
    integralFamily K (Pi.mulSingle i g) = RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K i g.val := by
  apply RestrictedProduct.ext
  intro j
  change (((Pi.mulSingle i g : ∀ i, K i) j) : G j) = (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K i g.val) j
  by_cases h : j = i
  · subst j
    rw [Pi.mulSingle_eq_same, RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same]
  · rw [Pi.mulSingle_eq_of_ne h, RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other K h]
    rfl

theorem cofinite (U : OpenSubgroup (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)) :
    ∀ᶠ i in Filter.cofinite, ∀ g ∈ K i, RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace K i g ∈ U := by
  have hopen : IsOpen ((integralFamily K) ⁻¹' (U : Set (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K))) :=
    U.isOpen.preimage (integralFamily_continuous K)
  have hone : (1 : ∀ i, K i) ∈ (integralFamily K) ⁻¹' (U : Set (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)) := by
    change integralFamily K 1 ∈ U
    rw [map_one]
    exact U.one_mem
  obtain ⟨S, V, hV, hsub⟩ := isOpen_pi_iff.mp hopen 1 hone
  have hS : ∀ᶠ i in Filter.cofinite, i ∉ S := by
    rw [Filter.eventually_cofinite]
    exact S.finite_toSet.subset (fun i hi => Classical.not_not.mp hi)
  filter_upwards [hS] with i hi
  intro g hg
  have hf : Pi.mulSingle i (⟨g, hg⟩ : K i) ∈ (S : Set I).pi V := by
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    rw [Pi.mulSingle_eq_of_ne hji]
    exact (hV j hj).2
  have hm := hsub hf
  change integralFamily K (Pi.mulSingle i (⟨g, hg⟩ : K i)) ∈ U at hm
  rwa [family_single] at hm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedOpenFactors.CM
