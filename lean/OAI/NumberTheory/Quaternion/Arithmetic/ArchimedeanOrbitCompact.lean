import OAI.NumberTheory.Quaternion.Arithmetic.OrbitScalar
import OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanVectorOrbit

/-! # Archimedean Orbit Compact -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanOrbitCompact

noncomputable section

/-! Compact Minkowski bounds on the orbit of a quaternion unit give
compact sets of archimedean norm-one points. -/

open scoped Classical _root_.NumberField _root_.Quaternion _root_.Matrix
open _root_.NumberField _root_.NumberField.mixedEmbedding Set QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]

def quaternionArchimedeanOrbit (a b : F) (r : ℍ[F,a,b]ˣ)
    (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ) : Fin 4 → mixedSpace F :=
  ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4 (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
    (fun i => mixedEmbedding F (linearEquivTuple a 0 b r.val i))

omit [NumberField F] in
theorem quaternionArchimedeanOrbit_continuous (a b : F) (r : ℍ[F,a,b]ˣ) :
    Continuous (quaternionArchimedeanOrbit a b r) :=
  ArchimedeanVectorOrbit.continuous_archimedean_vector_orbit (MatrixGroup.quaternionNormOneMatrixGroup a b) _

omit [NumberField F] in
theorem quaternionArchimedeanOrbit_local (a b : F) (r : ℍ[F,a,b]ˣ)
    (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ) (v : InfinitePlace F) :
    (fun i => MinkowskiLocalProjections.mixedCompletionProjection v (quaternionArchimedeanOrbit a b r h i)) =
      OrbitTopology.quaternionPointsOrbit a b (algebraMap F v.Completion)
        (FiniteOrbitCompact.quaternionScalarUnit (algebraMap F v.Completion) a b r) (h ⟨v, mem_univ v⟩) := by
  rw [quaternionArchimedeanOrbit, MinkowskiLocalProjections.mixedCompletionProjection_archimedean_vector]
  change _ = (h ⟨v, mem_univ v⟩).val.val *ᵥ
    linearEquivTuple _ 0 _ (ConjugationQuaternion.quaternionCoefficientMap (algebraMap F v.Completion) a b r.val)
  rw [OrbitScalar.quaternionCoefficientMap_coordinates]
  congr 1
  funext i
  exact RingHom.congr_fun (MinkowskiLocalProjections.mixedCompletionProjection_embedding v) (linearEquivTuple a 0 b r.val i)

omit [NumberField F] in
theorem quaternion_mixed_unit_coordinates_projection (a b : F) (r : ℍ[F,a,b]ˣ) (v : InfinitePlace F) :
    (fun i => MinkowskiLocalProjections.mixedCompletionProjection v (mixedEmbedding F (linearEquivTuple a 0 b r.val i))) =
      linearEquivTuple (algebraMap F v.Completion a) 0 (algebraMap F v.Completion b)
        (FiniteOrbitCompact.quaternionScalarUnit (algebraMap F v.Completion) a b r).val := by
  change _ = linearEquivTuple _ 0 _ (ConjugationQuaternion.quaternionCoefficientMap (algebraMap F v.Completion) a b r.val)
  rw [OrbitScalar.quaternionCoefficientMap_coordinates]
  funext i
  exact RingHom.congr_fun (MinkowskiLocalProjections.mixedCompletionProjection_embedding v) (linearEquivTuple a 0 b r.val i)

omit [NumberField F] in
theorem quaternionArchimedeanOrbit_projected_compact (a b : F) (r : ℍ[F,a,b]ˣ)
    (C : Set (Fin 4 → mixedSpace F)) (hC : IsCompact C) (v : InfinitePlace F) :
    IsCompact (OrbitTopology.quaternionPointsOrbit a b (algebraMap F v.Completion)
      (FiniteOrbitCompact.quaternionScalarUnit (algebraMap F v.Completion) a b r) ⁻¹'
        ((fun y : Fin 4 → mixedSpace F => fun i => MinkowskiLocalProjections.mixedCompletionProjection v (y i)) '' C)) := by
  have hπ : Continuous (fun y : Fin 4 → mixedSpace F => fun i => MinkowskiLocalProjections.mixedCompletionProjection v (y i)) :=
    continuous_pi (fun i => (MinkowskiLocalProjections.mixedCompletionProjection_continuous v).comp (continuous_apply i))
  let Cv : Set (Fin 4 → v.Completion) :=
    (fun y : Fin 4 → mixedSpace F => fun i => MinkowskiLocalProjections.mixedCompletionProjection v (y i)) '' C
  have hCv : IsCompact Cv := hC.image hπ
  have hc : IsCompact (OrbitTopology.quaternionPointsOrbit a b (algebraMap F v.Completion)
      (FiniteOrbitCompact.quaternionScalarUnit (algebraMap F v.Completion) a b r) ⁻¹' Cv) :=
    OrbitTopology.quaternionPointsOrbit_compact_preimage (K := v.Completion) a b (algebraMap F v.Completion)
      (FiniteOrbitCompact.quaternionScalarUnit (algebraMap F v.Completion) a b r) Cv hCv
  exact hc

omit [NumberField F] in
theorem quaternionArchimedeanOrbit_local_compact (a b : F) (r : ℍ[F,a,b]ˣ)
    (C : Set (Fin 4 → mixedSpace F)) (hC : IsCompact C) (v : InfinitePlace F) :
    IsCompact {g : (MatrixGroup.quaternionNormOneMatrixGroup a b).AtPlace v |
      g.val.val *ᵥ (fun i => MinkowskiLocalProjections.mixedCompletionProjection v (mixedEmbedding F (linearEquivTuple a 0 b r.val i))) ∈
        (fun y : Fin 4 → mixedSpace F => fun i => MinkowskiLocalProjections.mixedCompletionProjection v (y i)) '' C} := by
  have hc := quaternionArchimedeanOrbit_projected_compact a b r C hC v
  rw [quaternion_mixed_unit_coordinates_projection]
  exact hc

theorem quaternionArchimedeanOrbit_compact_preimage (a b : F) (r : ℍ[F,a,b]ˣ)
    (C : Set (Fin 4 → mixedSpace F)) (hC : IsCompact C) :
    IsCompact (quaternionArchimedeanOrbit a b r ⁻¹' C) := by
  have hc := ArchimedeanVectorOrbit.archimedean_vector_orbit_compact_preimage (MatrixGroup.quaternionNormOneMatrixGroup a b)
    (fun i => mixedEmbedding F (linearEquivTuple a 0 b r.val i)) C hC
    (quaternionArchimedeanOrbit_local_compact a b r C hC)
  exact hc

end

end OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanOrbitCompact
