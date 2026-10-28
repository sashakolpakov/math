import OAI.NumberTheory.Quaternion.Arithmetic.CompactQuotientProjection
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteIndex

/-! # Local Closure -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalClosure

noncomputable section

/-! Combine the finite-covolume and unipotent-generation steps of the local
closure argument. All intermediate assumptions are stated explicitly, and
none is supplied as an unproved fact about the Arithmetic arithmetic groups. -/

open scoped Classical

theorem dense_projected_subgroup_of_open_closure_additive_generation
    {K G L : Type*} [Field K] [CharZero K] [Group G] [Group L]
    [TopologicalSpace G] [TopologicalSpace L] [IsTopologicalGroup L]
    [SecondCountableTopology L]
    (f : G →* L) (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup G) (hΓ : CompactQuotientProjection.QuotientHasInvariantProbability Γ)
    (hopen : IsOpen ((Γ.map f).topologicalClosure : Set L))
    (hgen : Subgroup.closure (Arithmetic.FiniteIndex.additiveParameterElements (K := K) (G := L)) = ⊤) :
    Dense (Γ.map f : Set L) := by
  let : (Γ.map f).topologicalClosure.FiniteIndex :=
    CompactQuotientProjection.projectedClosure_finiteIndex f hf hsurj Γ hΓ hopen
  have htop := Arithmetic.FiniteIndex.finiteIndex_eq_top_of_additive_generation hgen (Γ.map f).topologicalClosure
  intro x
  change x ∈ (Γ.map f).topologicalClosure
  rw [htop]
  trivial

theorem dense_projected_sl2_subgroup_of_open_closure
    {K G : Type*} [Field K] [CharZero K] [TopologicalSpace K]
    [IsTopologicalRing K] [Group G] [TopologicalSpace G]
    [SecondCountableTopology (Matrix.SpecialLinearGroup (Fin 2) K)]
    (f : G →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup G) (hΓ : CompactQuotientProjection.QuotientHasInvariantProbability Γ)
    (hopen : IsOpen ((Γ.map f).topologicalClosure : Set (Matrix.SpecialLinearGroup (Fin 2) K))) :
    Dense (Γ.map f : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  let : (Γ.map f).topologicalClosure.FiniteIndex :=
    CompactQuotientProjection.projectedClosure_finiteIndex f hf hsurj Γ hΓ hopen
  have htop := Arithmetic.FiniteIndex.sl2_finiteIndex_eq_top (Γ.map f).topologicalClosure
  intro x
  change x ∈ (Γ.map f).topologicalClosure
  rw [htop]
  trivial

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalClosure
