import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MatrixSplitting

/-! # Small Index Matrix Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmallIndexMatrixSplitting

noncomputable section

/-! The geometric matrix criterion also applies to small finite index
types over a coefficient ring in any universe. Explicit index transport
keeps the residue-field criterion in the coefficient-ring universe. -/
universe u v w v' w'

theorem matrix_injective_submatrix_equiv
    {R : Type u} [CommRing R] {ι : Type v} {ν : Type w} {ι' : Type v'} {ν' : Type w'}
    [Fintype ι] [Fintype ν] [Fintype ι'] [Fintype ν']
    [DecidableEq ι] [DecidableEq ν] [DecidableEq ι'] [DecidableEq ν']
    (F : Matrix ι ν R) (e₁ : ι' ≃ ι) (e₂ : ν' ≃ ν)
    (hF : Function.Injective (Matrix.toLin' F)) :
    Function.Injective (Matrix.toLin' (F.submatrix e₁ e₂)) := by
  rw [Matrix.toLin'_submatrix]
  exact (LinearEquiv.funCongrLeft R R e₁).injective.comp
    (hF.comp (LinearEquiv.funCongrLeft R R e₂.symm).injective)

variable {R : Type u} [CommRing R]
variable {ι ν : Type} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem smallIndexMatrix_leftInverse_of_geometric_injective (F : Matrix ι ν R)
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K),
      Function.Injective (Matrix.toLin' (F.map φ))) :
    ∃ B : Matrix ν ι R, B * F = 1 := by
  let e₁ : ULift.{u} ι ≃ ι := Equiv.ulift
  let e₂ : ULift.{u} ν ≃ ν := Equiv.ulift
  let F' : Matrix (ULift.{u} ι) (ULift.{u} ν) R := F.submatrix e₁ e₂
  have hF' : ∀ (K : Type u) [Field K] [IsAlgClosed K] (φ : R →+* K),
      Function.Injective (Matrix.toLin' (F'.map φ)) := by
    intro K _ _ φ
    exact matrix_injective_submatrix_equiv (F.map φ) e₁ e₂ (hF K φ)
  obtain ⟨B, hB⟩ := Geometric.MatrixSplitting.matrix_leftInverse_of_geometric_injective F' hF'
  refine ⟨B.submatrix e₂.symm e₁.symm, ?_⟩
  change B.submatrix e₂.symm e₁.symm * F'.submatrix e₁.symm e₂.symm = 1
  rw [Matrix.submatrix_mul_equiv, hB]
  ext i j
  change (if e₂.symm i = e₂.symm j then (1 : R) else 0) = if i = j then 1 else 0
  simp only [e₂.symm.injective.eq_iff]

theorem smallIndexMatrix_injective_all_baseChanges_of_geometric_injective
    {C : Type u} [CommRing C] (φ : R →+* C) (F : Matrix ι ν R)
    (hF : ∀ (K : Type u) [Field K] [IsAlgClosed K] (ψ : R →+* K),
      Function.Injective (Matrix.toLin' (F.map ψ))) :
    Function.Injective (Matrix.toLin' (F.map φ)) := by
  obtain ⟨B, hB⟩ := smallIndexMatrix_leftInverse_of_geometric_injective F hF
  have hBA : B.map φ * F.map φ = 1 := by
    calc
      B.map φ * F.map φ = (B * F).map φ := Matrix.map_mul.symm
      _ = (1 : Matrix ν ν R).map φ := congrArg (fun M : Matrix ν ν R => M.map φ) hB
      _ = 1 := Matrix.map_one φ (map_zero φ) (map_one φ)
  have hlin : (Matrix.toLin' (B.map φ)).comp (Matrix.toLin' (F.map φ)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, hBA, Matrix.toLin'_one]
  have hleft : Function.LeftInverse (Matrix.toLin' (B.map φ)) (Matrix.toLin' (F.map φ)) :=
    fun x => LinearMap.congr_fun hlin x
  exact hleft.injective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SmallIndexMatrixSplitting
