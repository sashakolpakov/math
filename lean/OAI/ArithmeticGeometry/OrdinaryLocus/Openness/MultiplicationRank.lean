import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Multiplication Rank -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationRank.Construction

noncomputable section

/-! Constancy and positivity of the actual multiplication degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem multiplication_finrank_eq
    {k : Type*} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] (x y : A.left) :
    (Multiplication.Construction.multiplicationMap A n).left.finrank x = (Multiplication.Construction.multiplicationMap A n).left.finrank y := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  have : IsFinite (Multiplication.Construction.multiplicationMap A n).left :=
    Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A n
  have : Flat (Multiplication.Construction.multiplicationMap A n).left :=
    FieldMultiplicationFlat.Construction.flat_multiplication_of_isFinite_torsion_over_algClosed A n
  have : LocallyOfFinitePresentation (Multiplication.Construction.multiplicationMap A n).left :=
    FinitePresentation.Construction.locallyOfFinitePresentation_multiplication A n
  exact (Multiplication.Construction.multiplicationMap A n).left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace x y

theorem multiplication_finrank_pos
    {k : Type*} [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (n : ℕ) [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] (x : A.left) :
    0 < (Multiplication.Construction.multiplicationMap A n).left.finrank x := by
  have : IsFinite (Multiplication.Construction.multiplicationMap A n).left :=
    Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A n
  obtain ⟨hs, hf⟩ := FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A n
  have : Flat (Multiplication.Construction.multiplicationMap A n).left := hf
  have : Surjective (Multiplication.Construction.multiplicationMap A n).left := hs
  have h := ((Multiplication.Construction.multiplicationMap A n).left.one_le_finrank_iff_surjective.mpr hs) x
  exact h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationRank.Construction
