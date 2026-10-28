import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalColumnCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnBounds

/-! # Principal Column Decomposition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnDecomposition.CM

noncomputable section

/-! ThetaCycle: a principal congruence supplies actual lattice vectors for
both sets of column differences, and their literal local coefficients. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

theorem principal_columns_lattice_decomposition (B : HeckeCycles.GeometricSource.CM.BallDatum K) (d m k : ℤ)
    (hd : d ≠ 0) (hb : ∀ j : Fin 3, d • (Pi.single j (1 : K)) ∈ B.lattice)
    (N : ℕ) (hN : (N : ℤ) = d * m * k) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : B.principalLevel N g) :
    ∃ Y : Fin 2 → Fin 3 → HeckeCycles.GeometricSource.CM.Vec K, (∀ s j, Y s j ∈ B.lattice) ∧
      ∀ s j, LocalColumnCoordinates.CM.ballColumnDifferences K g s j = m • Y s j := by
  have he (s : Fin 2) (j : Fin 3) :
      ∃ y ∈ B.lattice, LocalColumnCoordinates.CM.ballColumnDifferences K g s j = m • y := by
    by_cases hs : s = 0
    · simpa only [LocalColumnCoordinates.CM.ballColumnDifferences, hs, ite_true] using
        PrincipalColumnBounds.CM.principal_column_difference K B d m k hd hb N hN g hg j
    · simpa only [LocalColumnCoordinates.CM.ballColumnDifferences, ite_eq_right hs] using
        PrincipalColumnBounds.CM.principal_column_difference K B d m k hd hb N hN g.symm (PrincipalColumnBounds.CM.principal_level_symm K B N g hg) j
  choose Y hY hdiff using he
  exact ⟨Y, hY, hdiff⟩

variable (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem local_ball_column_pair_of_integer_decomposition
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)
    (m : ℤ) (Y : Fin 2 → Fin 3 → HeckeCycles.GeometricSource.CM.Vec K)
    (hY : ∀ s j, LocalColumnCoordinates.CM.ballColumnDifferences K g s j = m • Y s j)
    (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield K)) :
    let q := RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
        (fun hb => (ne_of_lt B.negative) (by simp [hb]))) v
      (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)
    (q.val.val - 1, (q⁻¹).val.val - 1) =
      LocalUnitaryNeighborhoods.CM.quadraticMatrixPair (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) v (QuadraticModel.CM.cmQuadraticParameter K δ hδ))
        (fun p : Fin 2 × Fin 3 × Fin 3 × Fin 2 =>
          algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (maximalRealSubfield K) v) m *
            RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) v
              (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 p.2.2.2 (Y p.1 p.2.2.1 p.2.1))) := by
  dsimp only
  rw [LocalColumnCoordinates.CM.local_ball_column_pair]
  apply congrArg (LocalUnitaryNeighborhoods.CM.quadraticMatrixPair _)
  funext p
  rw [hY]
  change RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) v
    (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 p.2.2.2 (m • Y p.1 p.2.2.1 p.2.1)) = _
  rw [map_zsmul, map_zsmul, zsmul_eq_mul,
    show algebraMap ℤ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (maximalRealSubfield K) v) m =
      (m : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (maximalRealSubfield K) v) from map_intCast _ m]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalColumnDecomposition.CM
