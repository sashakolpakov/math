import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.DegreeMatrices

/-! # Degree Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeMatrices

noncomputable section

/-! A finite matrix presents every retained degree, including the zero relation modules below the generating degree. -/

universe u

variable {R : Type u} [CommRing R] {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (a : ι → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N))
variable (Q : Matrix ι (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) R)

def normalizedRetainedDegreeMatrix (d : ℕ) :
    Matrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d)
      (HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n (d - N)) R :=
  if hd : N ≤ d then
    Eq.mp (congrArg (fun e => Matrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n e)
      (HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n (d - N)) R)
        (Nat.sub_add_cancel hd)) (Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix a Q (d - N))
  else 0

omit [DecidableEq ι] in
theorem normalizedRetainedDegreeMatrix_above (d : ℕ) :
    (Matrix.toLin' (normalizedRetainedDegreeMatrix a Q (d + N))).range =
      (Matrix.toLin' (Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix a Q d)).range := by
  have h (e : ℕ) (he : e = d) (hrow : e + N = d + N) :
      (Matrix.toLin' (Eq.mp (congrArg (fun k => Matrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n k)
        (HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n e) R) hrow)
          (Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix a Q e))).range =
        (Matrix.toLin' (Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix a Q d)).range := by
    subst e
    rfl
  simp only [normalizedRetainedDegreeMatrix, dite_eq_left (Nat.le_add_left N d)]
  exact h _ (Nat.add_sub_cancel d N) (Nat.sub_add_cancel (Nat.le_add_left N d))

omit [DecidableEq ι] in
theorem normalizedRetainedDegreeMatrix_below (d : ℕ) (hd : d < N) :
    normalizedRetainedDegreeMatrix a Q d = 0 := by
  rw [normalizedRetainedDegreeMatrix, dite_eq_right (by omega)]

def normalizedRetainedDegreeMatrixCokernelEquiv (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (d : ℕ) :
    ((HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n d → R) ⧸ (Matrix.toLin' (normalizedRetainedDegreeMatrix a Q d)).range) ≃ₗ[R]
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d ⧸
        Single.DegreeRelationExtension.singleDegreePiece N (Normalized.HomogeneousGenerators.normalizedHomogeneousRelations Q) d) := by
  apply Classical.choice
  by_cases hd : N ≤ d
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    rw [Nat.add_comm N e, normalizedRetainedDegreeMatrix_above]
    exact ⟨Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrixCokernelEquiv a Q hQ e⟩
  · have hlt : d < N := by omega
    rw [normalizedRetainedDegreeMatrix_below a Q d hlt, map_zero, LinearMap.range_zero,
      Single.DegreeRelationExtension.singleDegreePiece_below N (Normalized.HomogeneousGenerators.normalizedHomogeneousRelations Q) d hlt]
    exact ⟨(Submodule.quotEquivOfEqBot _ rfl).trans
      ((Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d R).symm.trans
        (Submodule.quotEquivOfEqBot _ rfl).symm)⟩

omit [DecidableEq ι] in
theorem normalizedRetainedDegreeMatrix_map {A : Type u} [CommRing A] (φ : R →+* A) (d : ℕ) :
    (normalizedRetainedDegreeMatrix a Q d).map φ = normalizedRetainedDegreeMatrix a (Q.map φ) d := by
  by_cases hd : N ≤ d
  · have h (e k : ℕ) (hk : e + N = k) :
        (Eq.mp (congrArg (fun j => Matrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n j)
          (HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n e) R) hk)
            (Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix a Q e)).map φ =
        Eq.mp (congrArg (fun j => Matrix (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n j)
          (HilbertScheme.Presentations.Homogeneous.DegreeMatrix.GradedHilbert.DegreeRelationIndex (ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N)) n e) A) hk)
            (Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix a (Q.map φ) e) := by
      subst k
      exact Normalized.DegreeMatrices.normalizedHomogeneousDegreeMatrix_map a Q φ e
    simp only [normalizedRetainedDegreeMatrix, dite_eq_left hd]
    exact h (d - N) d (Nat.sub_add_cancel hd)
  · rw [normalizedRetainedDegreeMatrix_below a Q d (by omega),
      normalizedRetainedDegreeMatrix_below a (Q.map φ) d (by omega)]
    exact Matrix.map_zero φ φ.map_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeMatrices
