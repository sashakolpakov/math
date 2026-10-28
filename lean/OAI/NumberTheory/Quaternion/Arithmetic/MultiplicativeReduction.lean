import OAI.NumberTheory.Quaternion.Arithmetic.FiniteNormValues
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteKernelRepresentatives

/-! # Multiplicative Reduction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MultiplicativeReduction

noncomputable section

/-! Finitely many rational quaternion units, together with a compact
archimedean set, suffice after rational norm-one correction. -/

open scoped Classical _root_.NumberField _root_.Quaternion
open _root_.NumberField _root_.NumberField.mixedEmbedding Set QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_nonsplit_finite_multiplicative_reduction (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    ∃ C : Set (Fin 4 → mixedSpace F), IsCompact C ∧
      ∃ R : Set (ℍ[F,a,b]ˣ), R.Finite ∧
      ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b))
        (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ),
        ∃ q : (Norm.quaternionUnitNorm a b).ker, ∃ r ∈ R,
          let x := linearEquivTuple a 0 b (q.val.val * r.val)
          x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g) ∧
          ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
            (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
              (fun i => mixedEmbedding F (x i)) ∈ C := by
  obtain ⟨C, hC, T, hT, hT0, hv⟩ := FiniteNormValues.quaternion_nonsplit_finite_short_norm_values a b ha hs
  obtain ⟨R, hR, hrep⟩ := FiniteKernelRepresentatives.quaternion_finite_norm_representatives a b T hT
  refine ⟨C, hC, R, hR, ?_⟩
  intro g h
  obtain ⟨x, hx, hn, hc⟩ := hv g h
  let u := Norm.quaternionUnitOfNormNeZero a b (MatrixGroup.quaternionOfCoordinates a b x) (hT0 _ hn)
  obtain ⟨r, hr, q, he⟩ := hrep u hn
  have hcoords : linearEquivTuple a 0 b (q.val.val * r.val) = x := by
    have he' : q.val.val * r.val = MatrixGroup.quaternionOfCoordinates a b x := congrArg Units.val he
    rw [he']
    exact (linearEquivTuple a 0 b).apply_symm_apply x
  refine ⟨q, r, hr, ?_⟩
  dsimp only
  rw [hcoords]
  exact ⟨hx, hc⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.MultiplicativeReduction
