import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Components -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Components

/-!
NeighborCounting component-label bridge. HenselianLifting and SchematicClosure appear as explicit hypotheses
with their stated algebraic meanings. No statement stub is imported.
For an idempotent labeling an open-and-closed component, its restriction
to the subgroup closure vanishes in the special fiber exactly when its
restriction to the generic subgroup vanishes. Thus the set of occupied
component labels is preserved, which does not follow from rank alone.
-/

open scoped TensorProduct

universe u

def IdempotentLiftingInput (R B : Type u) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B] : Prop :=
  ∀ e₀ : B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B),
    IsIdempotentElem e₀ →
    ∃! e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) e = e₀

theorem idempotent_special_zero_iff
    (R B : Type u) [CommRing R] [IsLocalRing R]
    [CommRing B] [Algebra R B]
    (h_HenselianLifting : IdempotentLiftingInput R B)
    (e : B) (he : IsIdempotentElem e) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) e = 0 ↔
      e = 0 := by
  constructor
  · intro hzero
    obtain ⟨a, _, ha⟩ := h_HenselianLifting 0 (by simp [IsIdempotentElem])
    exact (ha e ⟨he, hzero⟩).trans (ha 0 ⟨by simp [IsIdempotentElem], by simp⟩).symm
  · rintro rfl
    exact map_zero _

theorem closure_component_label_preserved
    {R K A : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Flat R A]
    (I : Ideal (K ⊗[R] A)) [Ideal.IsHopfIdeal K I]
    (h_HenselianLifting : ∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B],
      IdempotentLiftingInput R B)
    (h_SchematicClosure :
      let ι : A →+* K ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
      let J : Ideal A := Ideal.comap ι I
      Ideal.IsHopfIdeal R J ∧
        Module.Finite R (A ⧸ J) ∧
        Module.Flat R (A ⧸ J) ∧
        Ideal.map ι J = I ∧
        Module.finrank R (A ⧸ J) = Module.finrank K ((K ⊗[R] A) ⧸ I))
    (e : A) (he : IsIdempotentElem e) :
    let ι : A →+* K ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
    let J : Ideal A := Ideal.comap ι I
    let B := A ⧸ J
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B))
        (Ideal.Quotient.mk J e) = 0 ↔
      Ideal.Quotient.mk I (ι e) = 0 := by
  let ι : A →+* K ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  let J : Ideal A := Ideal.comap ι I
  let B := A ⧸ J
  have hfinite : Module.Finite R B := h_SchematicClosure.2.1
  let := hfinite
  change
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R B))
        (Ideal.Quotient.mk J e) = 0 ↔
      Ideal.Quotient.mk I (ι e) = 0
  rw [idempotent_special_zero_iff R B (h_HenselianLifting B) _ (he.map (Ideal.Quotient.mk J))]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  rfl

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Components
