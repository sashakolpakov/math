import OAI.NumberTheory.Quaternion.Arithmetic.ArchimedeanOrbitCompact
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeLocalCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction

/-! # Adelic Orbit Correction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicOrbitCorrection

noncomputable section

/-! Rational norm-one multiplication converts the reduced lattice
vector bounds into bounds on actual adelic group points. -/

open scoped Classical _root_.NumberField _root_.Quaternion _root_.Matrix
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_finite_orbit_correction (a b : F) (r : ℍ[F,a,b]ˣ)
    (q : (Norm.quaternionUnitNorm a b).ker) (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b))
    (hx : linearEquivTuple a 0 b (q.val.val * r.val) ∈
      FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g)) :
    ∀ v, (g * FiniteAdelicComparison.diagonalFiniteAdelic (MatrixGroup.quaternionNormOneMatrixGroup a b)
      (MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q)) v ∈ FiniteOrbitCompact.quaternionFiniteOrbitBox a b r v := by
  intro v i
  have he := congrFun (OrbitScalar.quaternionPointsOrbit_diagonal_mul a b (LocalAdeles.localEmbedding (.inr v)) r q (g v)) i
  exact he.symm ▸ (AdelicLatticeLocalCoordinates.finiteAdelicGroupLattice_mem_iff (MatrixGroup.quaternionNormOneMatrixGroup a b) g _).mp hx v i

omit [NumberField F] in
theorem quaternion_archimedean_orbit_correction (a b : F) (r : ℍ[F,a,b]ˣ)
    (q : (Norm.quaternionUnitNorm a b).ker)
    (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ) :
    ArchimedeanOrbitCompact.quaternionArchimedeanOrbit a b r
      (h * (MatrixGroup.quaternionNormOneMatrixGroup a b).diagonal Set.univ
        (MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q)) =
      ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
        (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
          (fun i => mixedEmbedding F (linearEquivTuple a 0 b (q.val.val * r.val) i)) := by
  let p := MatrixGroup.quaternionMatrixPointsEquiv a b (RingHom.id F) q
  change ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
    ((ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val *
      ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap F 4 p.val) (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) 4 (linearEquivTuple a 0 b r.val)) = _
  rw [map_mul]
  change ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
    (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
    (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4 (ArithmeticGroups.Lattices.Archimedean.ExteriorAction.Construction.fullArchimedeanSLMap F 4 p.val)
      (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) 4 (linearEquivTuple a 0 b r.val))) = _
  rw [ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction.archimedeanRealRepresentation_diagonal]
  change ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
    (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
      (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) 4
        (MatrixQuaternionDet.quaternionRegularMatrix a b q.val.val *ᵥ linearEquivTuple a 0 b r.val)) = _
  rw [OrbitScalar.quaternionRegularMatrix_mul_coordinates]
  rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicOrbitCorrection
