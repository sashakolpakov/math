import OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLatticeFrames
import OAI.NumberTheory.Quaternion.Arithmetic.LatticeCovolumeTransport

/-! # Adelic Lattice Covolume -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeCovolume

noncomputable section

/-! All finite-adelic lattices coming from the actual special-linear
matrix realization have the same Minkowski covolume as the standard lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding _root_.MeasureTheory

variable {F : Type} [Field F] [NumberField F] {n : ℕ} [Nontrivial (Fin n)]

theorem finiteAdelicGroupLattice_covolume (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (μ : Measure (Fin n → mixedSpace F)) [Measure.IsAddHaarMeasure μ] :
    ZLattice.covolume (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g))) μ =
      ZLattice.covolume (ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module) μ := by
  obtain ⟨e, he, hL⟩ := MinkowskiLatticeFrames.finiteAdelicGroupLattice_minkowski_frame G g
  let L := ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module
  let : DiscreteTopology L := ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage_discrete _ (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).finite
  let : IsZLattice ℝ L := ⟨ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_full F n⟩
  let : BorelSpace (Fin n → mixedSpace F) := Pi.borelSpace
  rw [hL]
  exact LatticeCovolumeTransport.lattice_covolume_map_det_one L e he μ

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeCovolume
