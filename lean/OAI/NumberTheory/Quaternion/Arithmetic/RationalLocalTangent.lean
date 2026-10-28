import OAI.NumberTheory.Quaternion.Arithmetic.RationalLieLocalTangents
import OAI.NumberTheory.Quaternion.Arithmetic.ProductLocalSpan

/-! # Rational Local Tangent -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RationalLocalTangent

noncomputable section

/-! Weak approximation on scalars implies that the tangent span of
the rational-point closure contains every local infinitesimal direction. -/

open scoped Classical _root_.Matrix.Norms.Operator
open Set

attribute [local instance] LieRing.ofAssociativeRing

theorem rational_closure_tangentSpan_contains_local_infinitesimals
    {F : Type} [Field F] [CharZero F] {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : Type*} [NontriviallyNormedField κ] [CompleteSpace κ] {K : ι → Type}
    [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra F (K i)] [∀ i, Algebra κ (K i)]
    [∀ i, CompleteSpace (K i)] [∀ i, FiniteDimensional κ (K i)] [∀ i, ContinuousSMul κ (K i)]
    {n : ℕ} [Nonempty (Fin n)]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (hdense : DenseRange (fun r : F => fun i => algebraMap F (K i) r))
    (C : Set (∀ i, Matrix (Fin n) (Fin n) (K i))) (hC : IsClosed C)
    (hrational : ∀ g : G.RationalPoints,
      (fun i => (PolynomialGaloisNorm.matrixPointsHom G (RingHom.id F) g).map (algebraMap F (K i))) ∈ C)
    (X : ∀ i, Matrix (Fin n) (Fin n) (K i))
    (hX : ∀ i, X i ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F (K i)))) :
    X ∈ Submodule.span κ (tangentConeAt κ C 1) := by
  let W := Submodule.span κ (tangentConeAt κ C 1)
  let s := fun i => (fun S : Matrix (Fin n) (Fin n) F => S.map (algebraMap F (K i))) ''
    (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G : Set (Matrix (Fin n) (Fin n) F))
  apply ProductLocalSpan.product_mem_of_local_spans (K := K) W s ?_ X ?_
  · rintro i _ ⟨S, hS, rfl⟩ c
    have h := RationalLieLocalTangents.rational_infinitesimal_local_multiples_mem_tangentSpan
      (κ := κ) (K := K) G hG hsemi S hS (Pi.single i c) hdense C hC hrational
    have he : (fun j => Pi.single i c j • S.map (algebraMap F (K j))) =
        LinearMap.single κ (fun j => Matrix (Fin n) (Fin n) (K j)) i
          (c • S.map (algebraMap F (K i))) := by
      funext j
      by_cases hij : i = j
      · subst j
        simp only [Pi.single_eq_same, LinearMap.single_apply]
      · simp [LinearMap.single_apply, hij]
    exact he ▸ h
  · intro i
    have hi : X i ∈ (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer
      (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F (K i)))).toSubmodule := hX i
    exact ArithmeticGroups.Lattices.Infinitesimal.TangentExtension.Construction.infinitesimalStabilizer_eq_span_base (K := K i) G hG ▸ hi

end

end OAI.NumberTheory.Quaternion.Arithmetic.RationalLocalTangent
