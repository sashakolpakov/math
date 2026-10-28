import OAI.NumberTheory.PadicHodge.GeometricComparison.FittingGeneralized
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectionProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.Intersection

/-! # Hecke Projection -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeProjection.GeneralizedHecke

noncomputable section

/-! Simultaneous generalized eigenspaces of arbitrary commuting families are ranges of filtration-preserving commuting projections. -/

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem finite_projection (T : I → Module.End K V) (χ : I → K)
    (hpair : ∀ i j, Commute (T i) (T j)) (s : Finset I) :
    ∃ P : Module.End K V,
      IsIdempotentElem P ∧ P.range = (⨅ i ∈ s, (T i).maxGenEigenspace (χ i)) ∧
      (∀ Z : Module.End K V, (∀ i ∈ s, Commute (T i) Z) → Commute P Z) ∧
      (∀ U : Submodule K V, (∀ i ∈ s, U ≤ U.comap (T i)) → U ≤ U.comap P) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_, ?_, ?_⟩
      · exact one_mul 1
      · simp
        exact LinearMap.range_eq_top.mpr (fun x => ⟨x, rfl⟩)
      · intro Z _
        exact Commute.one_left Z
      · intro U _
        exact le_rfl
  | @insert i s hi ih =>
      obtain ⟨P, hP, hPrange, hPcomm, hPpres⟩ := ih
      let Q := FittingGeneralized.GeneralizedHecke.eigenProjection (T i) (χ i)
      have hQ : IsIdempotentElem Q := FittingGeneralized.GeneralizedHecke.eigenProjection_idempotent (T i) (χ i)
      have hc : Commute Q P := FittingGeneralized.GeneralizedHecke.eigenProjection_commutes (T i) P (χ i)
        (hPcomm (T i) (fun j _ => hpair j i)).symm
      refine ⟨Q * P, ProjectionProduct.GeneralizedHecke.projection_mul_idempotent Q P hQ hP hc, ?_, ?_, ?_⟩
      · rw [ProjectionProduct.GeneralizedHecke.projection_mul_range Q P hQ hP hc, hPrange, Finset.iInf_insert]
        exact congrArg (fun S : Submodule K V => S ⊓ ⨅ j ∈ s, (T j).maxGenEigenspace (χ j))
          (FittingGeneralized.GeneralizedHecke.eigenProjection_range (T i) (χ i))
      · intro Z hZ
        exact (FittingGeneralized.GeneralizedHecke.eigenProjection_commutes (T i) Z (χ i) (hZ i (Finset.mem_insert_self i s))).mul_left
          (hPcomm Z (fun j hj => hZ j (Finset.mem_insert_of_mem hj)))
      · intro U hU
        exact ProjectionProduct.GeneralizedHecke.product_preserves Q P U
          (FittingGeneralized.GeneralizedHecke.eigenProjection_preserves (T i) (χ i) U (hU i (Finset.mem_insert_self i s)))
          (hPpres U (fun j hj => hU j (Finset.mem_insert_of_mem hj)))

theorem simultaneous_projection (T : I → Module.End K V) (χ : I → K)
    (hpair : ∀ i j, Commute (T i) (T j)) :
    ∃ P : Module.End K V,
      IsIdempotentElem P ∧ P.range = Linear.generalizedHeckeSummand T χ ∧
      (∀ Z : Module.End K V, (∀ i, Commute (T i) Z) → Commute P Z) ∧
      (∀ U : Submodule K V, (∀ i, U ≤ U.comap (T i)) → U ≤ U.comap P) := by
  obtain ⟨s, hs⟩ := Finite.Intersection.GeneralizedHecke.finite_intersection (fun i => (T i).maxGenEigenspace (χ i))
  obtain ⟨P, hP, hPrange, hPcomm, hPpres⟩ := finite_projection T χ hpair s
  exact ⟨P, hP, hPrange.trans hs, fun Z hZ => hPcomm Z (fun i _ => hZ i),
    fun U hU => hPpres U (fun i _ => hU i)⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeProjection.GeneralizedHecke
