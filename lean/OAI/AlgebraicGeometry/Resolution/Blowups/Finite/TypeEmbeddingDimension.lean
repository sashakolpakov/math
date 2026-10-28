import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeDimension

/-! # Type Embedding Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeEmbeddingDimension.Construction

noncomputable section

/-! Actual embeddings bound dimension even for disconnected finite-type rings. -/

universe u

/-- An embedded domain survives in some actual prime quotient of the
target. This does not require the embedding to be integral. -/
theorem exists_prime_quotient_injective_of_domain_embedding (k : Type u) [CommRing k]
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) :
    ∃ q : Ideal B, q.IsPrime ∧ Function.Injective ((Ideal.Quotient.mkₐ k q).comp f) := by
  have hker : (⊥ : Ideal B).comap f.toRingHom ≤ (⊥ : Ideal A) := by
    rw [← RingHom.ker_eq_comap_bot]
    exact ((RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hf).le
  obtain ⟨q, _, hq, hcomap⟩ := Ideal.exists_ideal_comap_le_prime (f := f.toRingHom) (⊥ : Ideal A)
    (⊥ : Ideal B) hker
  refine ⟨q, hq, ?_⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply Ideal.mem_bot.mp
  apply hcomap
  change f (x - y) ∈ q
  rw [map_sub]
  exact Ideal.Quotient.eq.mp hxy

/-- The target may have zero divisors: a prime quotient retaining the
embedded domain already has at least the source's dimension. -/
theorem finiteType_domain_ringKrullDim_le_of_embedding (k : Type u) [Field k]
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) : ringKrullDim A ≤ ringKrullDim B := by
  obtain ⟨q, hq, hquot⟩ := exists_prime_quotient_injective_of_domain_embedding k f hf
  let : q.IsPrime := hq
  exact (TypeDimension.Construction.finiteType_domain_ringKrullDim_le_of_injective k ((Ideal.Quotient.mkₐ k q).comp f)
    hquot).trans (ringKrullDim_quotient_le q)

/-- Every actual embedding between finite-type algebras over a field
preserves the direction of the dimension bound, including zero rings and
disconnected rings. -/
theorem finiteType_ringKrullDim_le_of_injective (k : Type u) [Field k]
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FiniteType k A] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) : ringKrullDim A ≤ ringKrullDim B := by
  nontriviality A
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hint⟩
  rw [DivisorClass.Chern.IntegralDimension.Construction.integral_ringKrullDim_eq (R := P) (S := A) hg]
  exact finiteType_domain_ringKrullDim_le_of_embedding k (f.comp g) (hf.comp hg)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeEmbeddingDimension.Construction
