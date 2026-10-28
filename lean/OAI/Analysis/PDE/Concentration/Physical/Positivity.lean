import OAI.Analysis.PDE.Concentration.Physical.Current

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem nullMatrixReindex_isHermitian {d : ℕ}
    {M : OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ} (hM : Matrix.IsHermitian M) :
    Matrix.IsHermitian (nullMatrixReindex d M) :=
  hM.submatrix (nullIndexEquiv d)

theorem nullMatrixReindex_posSemidef {d : ℕ}
    {M : OAI.Analysis.Calculus.Current.Index d → OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ} (hM : (OAI.LinearAlgebra.Moore.complexify M).PosSemidef) :
    (OAI.LinearAlgebra.Moore.complexify (nullMatrixReindex d M)).PosSemidef :=
  hM.submatrix (fun p : Fin (d + 2) × Fin 2 => (nullIndexEquiv d p.1, p.2))

theorem matrixConjugationCLM_isHermitian {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hM : Matrix.IsHermitian M) :
    Matrix.IsHermitian (matrixConjugationCLM R M) :=
  Matrix.isHermitian_conjTranspose_mul_mul (OAI.Analysis.PDE.Dirichlet.realLift R) hM

theorem matrixConjugationCLM_posSemidef {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    {M : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hM : (OAI.LinearAlgebra.Moore.complexify M).PosSemidef) :
    (OAI.LinearAlgebra.Moore.complexify (matrixConjugationCLM R M)).PosSemidef := by
  change (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * M * OAI.Analysis.PDE.Dirichlet.realLift R)).PosSemidef
  rw [OAI.LinearAlgebra.Moore.complexify_mul, OAI.LinearAlgebra.Moore.complexify_mul, OAI.LinearAlgebra.Moore.complexify_star]
  exact hM.conjTranspose_mul_mul_same _

theorem physicalPacketCurrent_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    Matrix.IsHermitian (physicalPacketCurrent h a κ cR cI v x) := by
  apply matrixConjugationCLM_isHermitian
  apply nullMatrixReindex_isHermitian
  exact OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_isHermitian h a hh κ cR cI v _ _ hx

theorem physicalPacketCurrent_posSemidef {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    (OAI.LinearAlgebra.Moore.complexify (physicalPacketCurrent h a κ cR cI v x)).PosSemidef := by
  apply matrixConjugationCLM_posSemidef
  apply nullMatrixReindex_posSemidef
  exact OAI.Analysis.Calculus.Current.sourceRegularizedCurrent_posSemidef h a hh κ cR cI v _ _ hx

end OAI.Analysis.PDE.Concentration
