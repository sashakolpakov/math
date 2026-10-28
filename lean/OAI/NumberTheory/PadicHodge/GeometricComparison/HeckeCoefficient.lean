import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Hecke Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCoefficient.HeckeCoefficientAlgebras

noncomputable section

/-! Scalar towers determined by the actual place and the chosen embeddings of algebraic eigenvalues. -/

variable {K : Type} [Field K] {q : ℕ} [Fact q.Prime] (jq : K →+* ℚ_[q])

@[instance_reducible] def closureAlgebra : Algebra K (AlgebraicClosure ℚ_[q]) :=
  ((algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq).toAlgebra

@[instance_reducible] def coefficientAlgebra (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q])) : Algebra K L :=
  ((algebraMap ℚ_[q] L).comp jq).toAlgebra

theorem coefficientTower (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q])) :
    letI : Algebra K ℚ_[q] := jq.toAlgebra
    letI : Algebra K L := coefficientAlgebra jq L
    IsScalarTower K ℚ_[q] L := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : Algebra K L := coefficientAlgebra jq L
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem closureTower (L : IntermediateField ℚ_[q] (AlgebraicClosure ℚ_[q])) :
    letI : Algebra K L := coefficientAlgebra jq L
    letI : Algebra K (AlgebraicClosure ℚ_[q]) := closureAlgebra jq
    IsScalarTower K L (AlgebraicClosure ℚ_[q]) := by
  let : Algebra K L := coefficientAlgebra jq L
  let : Algebra K (AlgebraicClosure ℚ_[q]) := closureAlgebra jq
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact congrArg (fun f : ℚ_[q] →+* AlgebraicClosure ℚ_[q] => f (jq x))
    (IsScalarTower.algebraMap_eq ℚ_[q] L (AlgebraicClosure ℚ_[q]))

theorem algebraicClosureTower (κ : K →+* AlgebraicClosure ℚ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ) :
    letI : Algebra K (AlgebraicClosure ℚ) := κ.toAlgebra
    letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[q]) := ι.toAlgebra
    letI : Algebra K (AlgebraicClosure ℚ_[q]) := closureAlgebra jq
    IsScalarTower K (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[q]) := by
  let : Algebra K (AlgebraicClosure ℚ) := κ.toAlgebra
  let : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[q]) := ι.toAlgebra
  let : Algebra K (AlgebraicClosure ℚ_[q]) := closureAlgebra jq
  exact IsScalarTower.of_algebraMap_eq (fun x => DFunLike.congr_fun hplace x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCoefficient.HeckeCoefficientAlgebras
