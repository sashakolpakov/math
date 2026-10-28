import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions

/-! # Projective Compactness -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness

/-!
# The ordinary quotient topology on projective space

This module equips mathlib's projectivization with the quotient topology of its
nonzero vectors, with their given topology. It does not use the Zariski topology.
-/

section QuotientTopology

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V]

/-- The ordinary quotient topology on the lines of a topological vector space. -/
instance projectivizationTopologicalSpace : TopologicalSpace (Projectivization K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance

/-- The projection of nonzero vectors to their lines is a quotient map. -/
theorem isQuotientMap_projectivization_mk' :
    Topology.IsQuotientMap (Projectivization.mk' K : {v : V // v ≠ 0} →
      Projectivization K V) :=
  isQuotientMap_quotient_mk'

/-- The projection of nonzero vectors to projective space is continuous. -/
theorem continuous_projectivization_mk' :
    Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  continuous_coinduced_rng

/-- Openness is tested by pulling back to the nonzero-vector space. -/
theorem isOpen_projectivization_iff (s : Set (Projectivization K V)) :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s) :=
  (isQuotientMap_projectivization_mk' K V).isCoinducing.isOpen_preimage.symm

/-- Closedness is tested by pulling back to the nonzero-vector space. -/
theorem isClosed_projectivization_iff (s : Set (Projectivization K V)) :
    IsClosed s ↔ IsClosed ((Projectivization.mk' K) ⁻¹' s) :=
  (isQuotientMap_projectivization_mk' K V).isCoinducing.isClosed_preimage.symm

end QuotientTopology

variable (K V : Type*) [RCLike K] [NormedAddCommGroup V] [NormedSpace K V]

/-- Project a unit vector to its line. -/
def unitSphereToProjectivization : Metric.sphere (0 : V) 1 → Projectivization K V :=
  fun v => Projectivization.mk K v (ne_zero_of_mem_unit_sphere v)

/-- Unit-sphere projection is continuous for the ordinary quotient topology. -/
theorem continuous_unitSphereToProjectivization :
    Continuous (unitSphereToProjectivization K V) := by
  exact (continuous_projectivization_mk' K V).comp
    (continuous_subtype_val.subtype_mk (fun v => ne_zero_of_mem_unit_sphere v))

/-- Every projective line has a unit representative. -/
theorem unitSphereToProjectivization_surjective :
    Function.Surjective (unitSphereToProjectivization K V) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
      let w : Metric.sphere (0 : V) 1 :=
        ⟨(‖v‖⁻¹ : K) • v, by
          rw [mem_sphere_zero_iff_norm]
          exact norm_smul_inv_norm hv⟩
      refine ⟨w, ?_⟩
      apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
      exact ⟨(‖v‖⁻¹ : K), rfl⟩

/-- Finite-dimensional real or complex projective space is compact in its
ordinary quotient topology: it is the continuous image of the unit sphere. -/
instance projectivization_compactSpace [FiniteDimensional K V] :
    CompactSpace (Projectivization K V) := by
  let : ProperSpace V := FiniteDimensional.proper_rclike K V
  exact Function.Surjective.compactSpace
    (continuous_unitSphereToProjectivization K V)
    (unitSphereToProjectivization_surjective K V)

/-- Complex projective n-space, with its usual quotient topology, is compact. -/
theorem complexProjectiveSpace_compact (n : ℕ) :
    CompactSpace (Projectivization ℂ (Fin (n + 1) → ℂ)) :=
  inferInstance

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCompactness
