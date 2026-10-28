import OAI.NumberTheory.Quaternion.Arithmetic.StandardMinkowskiFrames
import OAI.NumberTheory.Quaternion.Arithmetic.AdelicGap

/-! # Adelic Lattice Mahler -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeMahler

noncomputable section

section

/-! The adelic lattice gap and determinant-one frames give compact
real matrix representatives by Mahler's theorem. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.Module Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [Nontrivial (Fin n)]

theorem adelic_lattice_compact_real_frames (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (h : G.ArchimedeanProduct Set.univ),
      ∀ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g), x ≠ 0 →
        ε ≤ ‖ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val
          (fun i => mixedEmbedding F (x i))‖) :
    ∃ K : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ (Fin n → mixedSpace F))) ℝ),
      IsCompact K ∧ ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (h : G.ArchimedeanProduct Set.univ),
        ∃ e : (Fin n → mixedSpace F) ≃ₗ[ℝ] (Fin n → mixedSpace F),
          e.toLinearMap.det = 1 ∧
          ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)) =
            (StandardMinkowskiFrames.standardMinkowskiLattice F n).map (e.toLinearMap.restrictScalars ℤ) ∧
          ∃ γ ∈ StandardMinkowskiFrames.standardMinkowskiIntegralMatrices F n, StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e * γ ∈ K := by
  obtain ⟨K, hK, hrep⟩ := ArithmeticGroups.Lattices.MahlerFrameNormed.Construction.exists_compact_matrix_lattice_representatives_normed
    (StandardMinkowskiFrames.standardMinkowskiLattice F n) (StandardMinkowskiFrames.standardMinkowskiIntegralBasis F n) ε hε
  refine ⟨K, hK, ?_⟩
  intro g h
  obtain ⟨e, he, hL⟩ := MinkowskiLatticeFrames.finiteAdelicGroupLattice_minkowski_frame G g
  refine ⟨e, he, hL, ?_⟩
  apply hrep (StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e)
  · rw [StandardMinkowskiFrames.adelicMinkowskiFrameMatrix_det G h e he, abs_one]
  · intro z hz hz0
    have hey : e z ∈ ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)) := by
      rw [hL]
      exact ⟨z, hz, rfl⟩
    obtain ⟨x, hx, hxe⟩ := hey
    have hx0 : x ≠ 0 := by
      intro hx0
      subst x
      have hez : e z = 0 := hxe.symm.trans (map_zero (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) n))
      exact hz0 (e.injective (hez.trans (map_zero e).symm))
    change ε ≤ ‖ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction (StandardMinkowskiFrames.standardMinkowskiRealBasis F n)
      (StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e) z‖
    rw [StandardMinkowskiFrames.adelicMinkowskiFrameMatrix_action]
    change ε ≤ ‖ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val (e z)‖
    rw [← hxe]
    exact hgap g h x hx hx0

theorem quaternion_nonsplit_compact_adelic_frames (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    ∃ K : Set (Matrix.GeneralLinearGroup (Fin (finrank ℝ (Fin 4 → mixedSpace F))) ℝ),
      IsCompact K ∧
      ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b))
        (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ),
        ∃ e : (Fin 4 → mixedSpace F) ≃ₗ[ℝ] (Fin 4 → mixedSpace F),
          e.toLinearMap.det = 1 ∧
          ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g)) =
            (StandardMinkowskiFrames.standardMinkowskiLattice F 4).map (e.toLinearMap.restrictScalars ℤ) ∧
          ∃ γ ∈ StandardMinkowskiFrames.standardMinkowskiIntegralMatrices F 4,
            StandardMinkowskiFrames.adelicMinkowskiFrameMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) h e * γ ∈ K := by
  obtain ⟨ε, hε, hgap⟩ := AdelicGap.quaternion_nonsplit_uniform_minkowski_gap a b ha hs
  exact adelic_lattice_compact_real_frames (MatrixGroup.quaternionNormOneMatrixGroup a b) ε hε hgap

end

/-! A compact set of lattice frames supplies a nonzero rational lattice
vector whose archimedean translate stays in a fixed compact set. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding Set

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem compact_adelic_vectors_of_compact_frames (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (z : Fin n → mixedSpace F) (hz : z ∈ StandardMinkowskiFrames.standardMinkowskiLattice F n) (hz0 : z ≠ 0)
    (K : Set (Matrix.GeneralLinearGroup (Fin (Module.finrank ℝ (Fin n → mixedSpace F))) ℝ))
    (hK : IsCompact K)
    (hframes : ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (h : G.ArchimedeanProduct Set.univ),
      ∃ e : (Fin n → mixedSpace F) ≃ₗ[ℝ] (Fin n → mixedSpace F),
        e.toLinearMap.det = 1 ∧
        ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)) =
          (StandardMinkowskiFrames.standardMinkowskiLattice F n).map (e.toLinearMap.restrictScalars ℤ) ∧
        ∃ γ ∈ StandardMinkowskiFrames.standardMinkowskiIntegralMatrices F n, StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e * γ ∈ K) :
    ∃ C : Set (Fin n → mixedSpace F), IsCompact C ∧
      ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (h : G.ArchimedeanProduct Set.univ),
        ∃ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g), x ≠ 0 ∧
          ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val
            (fun i => mixedEmbedding F (x i)) ∈ C := by
  let B := StandardMinkowskiFrames.standardMinkowskiRealBasis F n
  refine ⟨(fun M => ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B M z) '' K,
    hK.image (ArithmeticGroups.Lattices.MahlerFrameOf.Construction.continuous_matrixFrameAction B z), ?_⟩
  intro g h
  obtain ⟨e, _, hL, γ, hγ, hM⟩ := hframes g h
  have hγz : ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B γ z ∈ StandardMinkowskiFrames.standardMinkowskiLattice F n :=
    ((ArithmeticGroups.Lattices.StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameIntegralAction B)
      (StandardMinkowskiFrames.standardMinkowskiLattice F n) γ).mp hγ z).mpr hz
  have hey : e (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B γ z) ∈
      ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g)) := by
    rw [hL]
    exact ⟨_, hγz, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hey
  refine ⟨x, hx, ?_, StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e * γ, hM, ?_⟩
  · intro hx0
    subst x
    have hy0 : e (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B γ z) = 0 :=
      hxe.symm.trans (map_zero (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) n))
    have hγ0 := e.injective (hy0.trans (map_zero e).symm)
    exact hz0 ((ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B γ).injective (hγ0.trans (map_zero _).symm))
  · change ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B (StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e * γ) z = _
    rw [map_mul]
    change (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B (StandardMinkowskiFrames.adelicMinkowskiFrameMatrix G h e))
      (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B γ z) = _
    rw [StandardMinkowskiFrames.adelicMinkowskiFrameMatrix_action]
    change ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val
      (e (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction B γ z)) = _
    rw [← hxe]
    rfl

theorem quaternion_nonsplit_compact_adelic_vectors (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    ∃ C : Set (Fin 4 → mixedSpace F), IsCompact C ∧
      ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b))
        (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ),
        ∃ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g),
          x ≠ 0 ∧ ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
            (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
              (fun i => mixedEmbedding F (x i)) ∈ C := by
  obtain ⟨K, hK, hframes⟩ := quaternion_nonsplit_compact_adelic_frames a b ha hs
  let x : Fin 4 → F := Pi.basisFun F (Fin 4) 0
  let z := ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorMixedEmbedding (k := F) 4 x
  have hx : x ∈ (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F 4).module :=
    Submodule.subset_span (Set.mem_range_self 0)
  have hz : z ∈ StandardMinkowskiFrames.standardMinkowskiLattice F 4 := ⟨x, hx, rfl⟩
  have hz0 : z ≠ 0 := by
    intro he
    have h0 := congrFun he 0
    change mixedEmbedding F (x 0) = 0 at h0
    have hx0 : x 0 = 1 := by simp [x, Pi.basisFun_apply]
    rw [hx0, map_one] at h0
    exact one_ne_zero h0
  exact compact_adelic_vectors_of_compact_frames (MatrixGroup.quaternionNormOneMatrixGroup a b) z hz hz0 K hK hframes

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeMahler
