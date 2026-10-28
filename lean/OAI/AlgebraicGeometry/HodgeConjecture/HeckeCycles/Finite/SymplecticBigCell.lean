import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BigCellChoices

/-! # Symplectic Big Cell -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticBigCell.CM

noncomputable section

/-! Assemble integral local symmetric corrections into an actual
finite-adelic correction. The determinant has an adelic inverse, so
the corrected upper-left block is invertible over the adelic ring. -/

open scoped Classical RestrictedProduct _root_.Matrix
open Filter
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticLocal.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BigCellChoices.CM

variable {I : Type*} [Fintype I]

def adelicCorrection (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := fun i j =>
  ⟨fun v => BigCellChoices.CM.correction g v i j,
    (SymplecticLocal.CM.eventually_integral g).mono (fun v hv => BigCellChoices.CM.correction_integral g v hv i j)⟩

theorem adelicCorrection_symmetric (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : (adelicCorrection g).IsSymm := by
  apply Matrix.ext
  intro i j
  apply DFunLike.ext
  intro v
  exact congrFun (congrFun (BigCellChoices.CM.correction_symmetric g v) i) j

theorem adelicCorrection_eval (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    (adelicCorrection g).map (SymplecticLocal.CM.localEval v) = BigCellChoices.CM.correction g v := rfl

def determinant (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  (g.val.toBlocks₁₁ + adelicCorrection g * g.val.toBlocks₂₁).det

theorem determinant_eval (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    SymplecticLocal.CM.localEval v (determinant g) = BigCellChoices.CM.correctedDeterminant g v := by
  unfold determinant
  rw [RingHom.map_det, map_add, map_mul]
  rfl

def inverseDeterminant (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  ⟨fun v => (BigCellChoices.CM.correctedDeterminant g v)⁻¹,
    (SymplecticLocal.CM.eventually_integral g).mono (fun v hv => BigCellChoices.CM.inverse_integral g v hv)⟩

theorem determinant_mul_inverse (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : determinant g * inverseDeterminant g = 1 := by
  apply DFunLike.ext
  intro v
  change SymplecticLocal.CM.localEval v (determinant g) * (BigCellChoices.CM.correctedDeterminant g v)⁻¹ = 1
  rw [determinant_eval]
  exact mul_inv_cancel₀ (BigCellChoices.CM.correctedDeterminant_unit g v).ne_zero

def determinantUnit (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQfˣ where
  val := determinant g
  inv := inverseDeterminant g
  val_inv := determinant_mul_inverse g
  inv_val := by rw [mul_comm]; exact determinant_mul_inverse g

theorem exists_big_cell (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    ∃ B : Matrix I I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf, B.IsSymm ∧
      IsUnit (g.val.toBlocks₁₁ + B * g.val.toBlocks₂₁).det :=
  ⟨adelicCorrection g, adelicCorrection_symmetric g, ⟨determinantUnit g, rfl⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.SymplecticBigCell.CM
