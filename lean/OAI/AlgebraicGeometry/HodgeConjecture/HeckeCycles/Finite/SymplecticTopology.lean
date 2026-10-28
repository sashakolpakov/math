import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticRestriction

/-! # Symplectic Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticTopology.CM

noncomputable section

/-! Continuity of the actual assembled finite symplectic matrices and
their restriction of scalars, for the restricted-product topology. -/

open scoped Classical _root_.NumberField _root_.Matrix
open Filter _root_.Matrix

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

theorem assembled_entry (i j : Fin N ⊕ Fin N) :
    Continuous (fun g : HeckeCycles.NumberField.FiniteSymplectic.CM.Group F N =>
      HeckeCycles.NumberField.FiniteSymplectic.CM.matrix F N g i j) := by
  exact RestrictedProduct.mapAlong_continuous
    (fun v : HeckeCycles.NumberField.FiniteSymplectic.CM.Place F => RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic (v.adicCompletion F) N)
    (fun v : HeckeCycles.NumberField.FiniteSymplectic.CM.Place F => v.adicCompletion F)
    id tendsto_id (fun _ g => g.val i j)
    (Eventually.of_forall (fun _ g hg => hg.1 i j))
    (fun _ => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

theorem assembled_matrix : Continuous (fun g : HeckeCycles.NumberField.FiniteSymplectic.CM.Group F N =>
    (HeckeCycles.NumberField.FiniteSymplectic.CM.assemble F N g).val) :=
  continuous_pi (fun i => continuous_pi (fun j => assembled_entry F N i j))

theorem restriction_action
    {X : Type*} [TopologicalSpace X] (g : X → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
    (hg : Continuous (fun x => (g x).val))
    (v : (AdelicTestCoordinates.CM.Index F N ⊕ AdelicTestCoordinates.CM.Index F N) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    Continuous (fun x => (SymplecticRestriction.CM.restriction F N (g x)).val *ᵥ v) := by
  have he : (fun x => (SymplecticRestriction.CM.restriction F N (g x)).val *ᵥ v) =
      (fun x => TracePhase.CM.coordinates F N
        ((g x).val *ᵥ (TracePhase.CM.coordinates F N).symm v)) := by
    funext x
    exact SymplecticRestriction.CM.matrix_apply F N (g x) v
  rw [he]
  exact (TracePhase.CM.coordinates F N).continuous.comp (hg.matrix_mulVec continuous_const)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticTopology.CM
