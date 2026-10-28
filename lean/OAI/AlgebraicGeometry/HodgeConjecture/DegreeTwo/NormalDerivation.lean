import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalConormal
import Mathlib.RingTheory.Smooth.Basic

/-! # Normal Derivation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalDerivation.Constructions

noncomputable section

section

/-!
# DegreeTwo: a normalized normal derivation for a smooth principal hypersurface

Formal smoothness splits the actual conormal injection. Composing that
retraction with the principal conormal coefficient gives a derivation which
takes the defining parameter to one.
-/

open scoped TensorProduct

variable (K R : Type*) [CommRing K] [CommRing R] [IsDomain R] [Algebra K R]
variable [Algebra.FormallySmooth K R] (p : R) (hp : p ≠ 0)
variable [Algebra.FormallySmooth K (R ⧸ Ideal.span {p})]

include hp in
/-- A genuine derivation transverse to the smooth principal hypersurface,
normalized on its actual regular defining equation. -/
theorem exists_normalized_normal_derivation :
    ∃ δ : Derivation K R (R ⧸ Ideal.span {p}), δ p = 1 := by
  let I := Ideal.span ({p} : Set R)
  let B := R ⧸ I
  let J := RingHom.ker (algebraMap R B)
  have hJI : J = I := Ideal.mk_ker
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := K) (P := R) (A := B) Ideal.Quotient.mk_surjective).mp inferInstance
  let e := Ideal.Cotangent.equivOfEq J I hJI
  let ψ : B ⊗[R] KaehlerDifferential K R →ₗ[R] B :=
    (PrincipalConormal.Constructions.principalConormalCoefficient p hp).comp (e.toLinearMap.comp l)
  let φ : KaehlerDifferential K R →ₗ[R] B := ψ.comp (TensorProduct.mk R B (KaehlerDifferential K R) 1)
  let δ : Derivation K R B := KaehlerDifferential.linearMapEquivDerivation K R φ
  refine ⟨δ, ?_⟩
  have hpJ : p ∈ J := by
    rw [hJI]
    exact Ideal.subset_span (Set.mem_singleton p)
  have hlp := DFunLike.congr_fun hl (J.toCotangent ⟨p, hpJ⟩)
  change l (KaehlerDifferential.kerCotangentToTensor K R B (J.toCotangent ⟨p, hpJ⟩)) =
    J.toCotangent ⟨p, hpJ⟩ at hlp
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hlp
  change PrincipalConormal.Constructions.principalConormalCoefficient p hp (e (l (1 ⊗ₜ[R] KaehlerDifferential.D K R p))) = 1
  rw [hlp]
  change PrincipalConormal.Constructions.principalConormalCoefficient p hp
    (Ideal.Cotangent.equivOfEq J I hJI (J.toCotangent ⟨p, hpJ⟩)) = 1
  rw [Ideal.Cotangent.equivOfEq_toCotangent]
  exact PrincipalConormal.Constructions.principalConormalCoefficient_self p hp

end

/-!
# DegreeTwo: specialize the normalized normal derivation to a point

The point character factors through the actual principal quotient, so the
normal derivation retains its value one after evaluation at that point.
-/

variable (K R C : Type*) [CommRing K] [CommRing R] [IsDomain R] [CommRing C]
  [Algebra K R] [Algebra R C] [Algebra K C] [IsScalarTower K R C]
  [Algebra.FormallySmooth K R]
  (p : R) (hp : p ≠ 0) [Algebra.FormallySmooth K (R ⧸ Ideal.span {p})]
  (hpoint : algebraMap R C p = 0)

include hp hpoint in
/-- At any point of a smooth principal hypersurface, its defining parameter
has a point-valued algebraic derivation equal to one. -/
theorem exists_point_normal_derivation :
    ∃ δ : Derivation K R C, δ p = 1 := by
  let I := Ideal.span ({p} : Set R)
  have hI : I ≤ RingHom.ker (algebraMap R C) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpoint
  let χ : R ⧸ I →ₐ[R] C := Ideal.Quotient.liftₐ I (Algebra.ofId R C) (fun a ha => hI ha)
  obtain ⟨δ, hδ⟩ := exists_normalized_normal_derivation K R p hp
  refine ⟨χ.toLinearMap.compDer δ, ?_⟩
  change χ (δ p) = 1
  rw [hδ, map_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalDerivation.Constructions
