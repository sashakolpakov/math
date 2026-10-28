import OAI.NumberTheory.Quaternion.Arithmetic.OrbitReconstruction
import OAI.NumberTheory.Quaternion.Arithmetic.CompactReconstruction
import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact

/-! # Orbit Topology -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OrbitTopology

noncomputable section

/-! Quaternion norm-one orbits on units have compact inverse images
of compact coordinate sets. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open QuaternionAlgebra Set

variable {F K : Type} [Field F]

section Algebra
variable [Field K]

def quaternionPointsOrbit (a b : F) (ρ : F →+* K) (r : ℍ[K,ρ a,ρ b]ˣ)
    (g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ) : Fin 4 → K :=
  g.val.val *ᵥ linearEquivTuple (ρ a) 0 (ρ b) r.val

theorem quaternionPointsOrbit_continuous [TopologicalSpace K] [IsTopologicalRing K]
    (a b : F) (ρ : F →+* K) (r : ℍ[K,ρ a,ρ b]ˣ) :
    Continuous (quaternionPointsOrbit a b ρ r) := by
  have hm : Continuous (fun g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ => g.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact hm.matrix_mulVec continuous_const

end Algebra

theorem quaternionPointsOrbit_compact_preimage
    [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (a b : F) (ρ : F →+* K) (r : ℍ[K,ρ a,ρ b]ˣ)
    (C : Set (Fin 4 → K)) (hC : IsCompact C) :
    IsCompact (quaternionPointsOrbit a b ρ r ⁻¹' C) := by
  exact CompactReconstruction.isCompact_preimage_of_reconstruction
    (fun g : (MatrixGroup.quaternionNormOneMatrixGroup a b).Points ρ => g.val.val)
    ((MatrixGroup.quaternionNormOneMatrixGroup a b).points_isClosedEmbedding ρ)
    (quaternionPointsOrbit a b ρ r) (quaternionPointsOrbit_continuous a b ρ r)
    (OrbitReconstruction.quaternionOrbitRecovery (ρ a) (ρ b) r)
    (OrbitReconstruction.quaternionOrbitRecovery (ρ a) (ρ b) r).continuous_on_pi
    (OrbitReconstruction.quaternionOrbitRecovery_apply a b ρ r) C hC

end

end OAI.NumberTheory.Quaternion.Arithmetic.OrbitTopology
