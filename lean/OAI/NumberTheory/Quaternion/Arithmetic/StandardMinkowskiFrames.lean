import OAI.NumberTheory.Quaternion.Arithmetic.AdelicLatticeCovolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed

/-! # Standard Minkowski Frames -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.StandardMinkowskiFrames

noncomputable section

/-! Fixed integral and real coordinate frames for the standard
Minkowski lattice and for archimedean translates of adelic lattices. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.MahlerFrameNormed.Construction _root_.Module

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

def standardMinkowskiLattice : Submodule ℤ (Fin n → mixedSpace F) :=
  ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).module

instance standardMinkowskiLatticeDiscrete : DiscreteTopology (standardMinkowskiLattice F n) :=
  ArithmeticGroups.Lattices.IntegralLattice.Construction.vectorLatticeImage_discrete _ (ArithmeticGroups.Lattices.IntegralLattice.FullLattice.standard F n).finite

instance standardMinkowskiLatticeIsZLattice : IsZLattice ℝ (standardMinkowskiLattice F n) :=
  ⟨ArithmeticGroups.Lattices.Minkowski.IntegralAction.Construction.standard_vectorLatticeImage_full F n⟩

def standardMinkowskiIntegralBasis :
    Basis (Fin (finrank ℝ (Fin n → mixedSpace F))) ℤ (standardMinkowskiLattice F n) :=
  (Module.finBasis ℤ (standardMinkowskiLattice F n)).reindex
    (finCongr (ZLattice.rank ℝ (standardMinkowskiLattice F n)))

def standardMinkowskiRealBasis :
    Basis (Fin (finrank ℝ (Fin n → mixedSpace F))) ℝ (Fin n → mixedSpace F) :=
  (standardMinkowskiIntegralBasis F n).ofZLatticeBasis ℝ

def standardMinkowskiIntegralMatrices :
    Subgroup (Matrix.GeneralLinearGroup (Fin (finrank ℝ (Fin n → mixedSpace F))) ℝ) :=
  ArithmeticGroups.Lattices.SubmoduleOrbit.Construction.submoduleImageStabilizer (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameIntegralAction (standardMinkowskiRealBasis F n))
    (standardMinkowskiLattice F n)

variable {F n}

def adelicMinkowskiFrameMatrix (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (h : G.ArchimedeanProduct Set.univ)
    (e : (Fin n → mixedSpace F) ≃ₗ[ℝ] (Fin n → mixedSpace F)) :
    Matrix.GeneralLinearGroup (Fin (finrank ℝ (Fin n → mixedSpace F))) ℝ :=
  (ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction (standardMinkowskiRealBasis F n)).symm
    (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val * e)

theorem adelicMinkowskiFrameMatrix_action (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (h : G.ArchimedeanProduct Set.univ)
    (e : (Fin n → mixedSpace F) ≃ₗ[ℝ] (Fin n → mixedSpace F)) :
    ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction (standardMinkowskiRealBasis F n) (adelicMinkowskiFrameMatrix G h e) =
      ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val * e :=
  MulEquiv.apply_symm_apply _ _

theorem adelicMinkowskiFrameMatrix_det (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (h : G.ArchimedeanProduct Set.univ)
    (e : (Fin n → mixedSpace F) ≃ₗ[ℝ] (Fin n → mixedSpace F)) (he : e.toLinearMap.det = 1) :
    (adelicMinkowskiFrameMatrix G h e).val.det = 1 := by
  rw [← ArithmeticGroups.Lattices.LatticeFrameAction.Construction.matrixFrameAction_det (standardMinkowskiRealBasis F n), adelicMinkowskiFrameMatrix_action,
    LinearEquiv.coe_toLinearMap_mul, map_mul, ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation_det, he, one_mul]

end

end OAI.NumberTheory.Quaternion.Arithmetic.StandardMinkowskiFrames
