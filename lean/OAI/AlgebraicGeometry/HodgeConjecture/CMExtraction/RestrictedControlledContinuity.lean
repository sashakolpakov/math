import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Restricted Controlled Continuity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedControlledContinuity.Approximation

noncomputable section

/-! A map to a restricted product is continuous when its local maps are
continuous and finitely many continuous adele coordinates control its
integrality. This also applies to entries and inverse entries of matrices. -/

open scoped Classical RestrictedProduct
open Filter

theorem continuous_restricted_of_finite_controls
    {X I J : Type*} [TopologicalSpace X] [Finite J]
    {G : I → Type*} [∀ v, TopologicalSpace (G v)] (K : ∀ v, Set (G v))
    {R : J → I → Type*} [∀ j v, TopologicalSpace (R j v)]
    (S : ∀ j v, Set (R j v)) (hS : ∀ j v, IsOpen (S j v))
    (a : ∀ j, X → RestrictedProduct (R j) (S j) cofinite)
    (ha : ∀ j, Continuous (a j))
    (f : X → RestrictedProduct G K cofinite)
    (hf : ∀ v, Continuous (fun x => f x v))
    (hcontrol : ∀ x v, (∀ j, a j x v ∈ S j v) → f x v ∈ K v) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  let T : Set I := {v | ∀ j, a j x v ∈ S j v}
  have hT : cofinite ≤ principal T := by
    rw [le_principal_iff]
    exact eventually_all.mpr (fun j => (a j x).property)
  let U : Set X := {y | ∀ j, ∀ v ∈ T, a j y v ∈ S j v}
  have hU : IsOpen U := by
    have hUeq : U = ⋂ j, {y | ∀ v ∈ T, a j y v ∈ S j v} := by
      ext y
      simp only [U, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hUeq]
    apply isOpen_iInter_of_finite
    intro j
    exact (RestrictedProduct.isOpen_forall_imp_mem (hS j) (p := fun v => v ∈ T)).preimage (ha j)
  have hx : x ∈ U := fun j v hv => hv j
  let fT : U → RestrictedProduct G K (principal T) := fun y =>
    ⟨fun v => f y.val v, by
      rw [eventually_principal]
      intro v hv
      exact hcontrol y.val v (fun j => y.property j v hv)⟩
  have hfT : Continuous fT := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    exact continuous_pi (fun v => (hf v).comp continuous_subtype_val)
  have hrestrict : Continuous (fun y : U => f y.val) :=
    (RestrictedProduct.continuous_inclusion hT).comp hfT
  exact (continuousOn_iff_continuous_domRestrict.mpr hrestrict).continuousAt (hU.mem_nhds hx)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RestrictedControlledContinuity.Approximation
