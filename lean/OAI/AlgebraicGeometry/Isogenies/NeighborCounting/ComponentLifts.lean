import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Components
import OAI.Algebra.LocalRing.HenselianLifting
import OAI.AlgebraicGeometry.GroupSchemes.SchematicClosure

/-! # Component Lifts -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentLifts.Components

noncomputable section

/-!
Construct complete component idempotents by HenselianLifting and prove that SchematicClosure
closure preserves their occupied labels. The finite algebra carrying the
subgroup need not be etale.
-/

open scoped TensorProduct

universe u

abbrev ResidueAlgebra (R A : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] :=
  A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)

section Idempotents

variable (R A : Type u) [CommRing R] [HenselianLocalRing R]
  [CommRing A] [Algebra R A] [Module.Finite R A]

theorem idempotentLiftingInput : Components.IdempotentLiftingInput R A :=
  OAI.Algebra.LocalRing.HenselianLifting.Construction.idempotents_lift_uniquely R A

def liftIdempotent (e : ResidueAlgebra R A) (he : IsIdempotentElem e) : A :=
  (idempotentLiftingInput R A e he).choose

theorem liftIdempotent_idem (e : ResidueAlgebra R A) (he : IsIdempotentElem e) :
    IsIdempotentElem (liftIdempotent R A e he) :=
  (idempotentLiftingInput R A e he).choose_spec.1.1

theorem liftIdempotent_reduction (e : ResidueAlgebra R A) (he : IsIdempotentElem e) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))
      (liftIdempotent R A e he) = e :=
  (idempotentLiftingInput R A e he).choose_spec.1.2

theorem idempotent_eq_of_reduction_eq {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) e =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) f) : e = f := by
  let π := Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A))
  obtain ⟨a, _, ha⟩ := idempotentLiftingInput R A (π f) (hf.map π)
  exact (ha e ⟨he, h⟩).trans (ha f ⟨hf, rfl⟩).symm

variable {I : Type u} [Fintype I]

/-- All residue components lift simultaneously and remain disjoint and
exhaustive. The proof derives these relations from unique idempotent lifting. -/
theorem complete_component_lift (e : I → ResidueAlgebra R A)
    (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (fun i => liftIdempotent R A (e i) (he.idem i)) := by
  let d := fun i => liftIdempotent R A (e i) (he.idem i)
  have hd (i : I) : IsIdempotentElem (d i) := liftIdempotent_idem R A _ _
  have hred (i : I) :
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) (d i) = e i :=
    liftIdempotent_reduction R A _ _
  have ho : OrthogonalIdempotents d := by
    refine ⟨hd, ?_⟩
    intro i j hij
    apply (Components.idempotent_special_zero_iff R A (idempotentLiftingInput R A) (d i * d j)
      ((hd i).mul (hd j))).mp
    rw [map_mul, hred, hred]
    exact he.ortho hij
  refine ⟨ho, ?_⟩
  apply idempotent_eq_of_reduction_eq R A ho.isIdempotentElem_sum IsIdempotentElem.one
  simpa only [map_sum, hred, map_one] using he.complete

end Idempotents

/-- The component-label comparison now follows from proved HenselianLifting and SchematicClosure,
with no lifting or closure proposition passed in as a hypothesis. -/
theorem closure_labels_preserved
    (R A : Type u) [CommRing R] [HenselianLocalRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Flat R A]
    (L : Type u) [Field L] [Algebra R L] [IsFractionRing R L]
    (J : Ideal (L ⊗[R] A)) [Ideal.IsHopfIdeal L J]
    (e : A) (he : IsIdempotentElem e) :
    let ι : A →+* L ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
    let C := A ⧸ Ideal.comap ι J
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R C))
        (Ideal.Quotient.mk (Ideal.comap ι J) e) = 0 ↔
      Ideal.Quotient.mk J (ι e) = 0 :=
  Components.closure_component_label_preserved J (fun C _ _ _ => idempotentLiftingInput R C)
    (GroupSchemes.SchematicClosure.finite_flat_closure_of_generic_subgroup J) e he

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentLifts.Components
