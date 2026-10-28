import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GoodPrime

/-! # Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Frames.CM

noncomputable section

/-! The local field embeddings and lattice frames used for Hecke data
are obtained from the same completion and integral characters as CMPoints. -/

open scoped Classical
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
  (places : GeometricSource.CM.Places E)

def pairedEmbedding (v : Fin places.count × Bool) : E →+* ℚ_[q] :=
  (j.completion.toRingHom.comp (FinitePlace.embedding j.prime)).comp
    (iota.comp (PairedCompletion.CM.placeIndex E places v).toRingHom)

omit [IsGalois ℚ E] in
theorem pairedEmbedding_integral (v : Fin places.count × Bool)
    (a : RingOfIntegers E) :
    pairedEmbedding E j iota places v a =
      (PairedCompletion.CM.pairedCharacter E j iota places v a : ℚ_[q]) := by
  have h := DFunLike.congr_fun j.integral_compatibility
    (RingOfIntegers.mapRingHom (iota.comp (PairedCompletion.CM.placeIndex E places v).toRingHom) a)
  exact h.symm

omit [IsGalois ℚ E] in
/-- The bound depends only on the reference lattice. Every later split
prime supplies all conjugate frames through its actual completion. -/
theorem exists_paired_frame_bound (Λ : Submodule ℤ (Fin 3 → E))
    (hfg : Λ.FG) (hfull : Submodule.span ℚ (Λ : Set (Fin 3 → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ (p : ℕ) [Fact p.Prime], d < p →
      ∀ (j' : PELModuli.CMPoints.Arithmetic.QadicChoice K κ p)
        (v : Fin places.count × Bool),
      Lattice.CM.localLattice (pairedEmbedding E j' iota places v) Λ =
        Lattice.CM.standard (q := p) := by
  obtain ⟨d, hd, hframe⟩ := Lattice.CM.exists_uniform_local_frame Λ hfg hfull
  refine ⟨d, hd, ?_⟩
  intro p _ hp j' v
  exact hframe p (Nat.coprime_of_lt_prime hd.ne' hp (Fact.out : p.Prime))
    (pairedEmbedding E j' iota places v) (PairedCompletion.CM.pairedCharacter E j' iota places v)
    (pairedEmbedding_integral E j' iota places v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Frames.CM
