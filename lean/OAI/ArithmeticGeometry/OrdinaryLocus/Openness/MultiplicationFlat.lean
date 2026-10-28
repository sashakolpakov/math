import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat

/-! # Multiplication Flat -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationFlat.Construction

noncomputable section

/-! Flatness of finite multiplication maps in the Openness family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- Finite multiplication maps on a smooth proper commutative group with
geometrically connected fibers are flat over their target. -/
theorem flat_multiplication_of_isFinite (n : ℕ)
    [IsFinite (Multiplication.Construction.multiplicationMap A n).left] : Flat (Multiplication.Construction.multiplicationMap A n).left := by
  have : LocallyOfFinitePresentation (Multiplication.Construction.multiplicationMap A n).left :=
    FinitePresentation.Construction.locallyOfFinitePresentation_multiplication A n
  apply FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges (Multiplication.Construction.multiplicationMap A n)
  intro K _ _ t
  let F := Over.pullback t
  let B := F.obj A
  have : Smooth B.hom := by change Smooth (pullback.snd A.hom t); infer_instance
  have : IsProper B.hom := by change IsProper (pullback.snd A.hom t); infer_instance
  have : GeometricallyConnected B.hom := by
    change GeometricallyConnected (pullback.snd A.hom t)
    infer_instance
  have hp : F.map (Multiplication.Construction.multiplicationMap A n) = Multiplication.Construction.multiplicationMap B n := by
    exact ((F.homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n).trans
      (congrArg (fun k => k ^ n) (F.map_id A))
  have hfin : IsFinite (F.map (Multiplication.Construction.multiplicationMap A n)).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) t (Multiplication.Construction.multiplicationMap A n) inferInstance
  rw [hp] at hfin
  have hf : Flat (Multiplication.Construction.multiplicationMap B n).left :=
    (FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite B n).2
  change Flat (F.map (Multiplication.Construction.multiplicationMap A n)).left
  rwa [hp]

/-- A finite torsion kernel in the Openness family is flat over the base,
as the pullback of its flat multiplication map along the identity. -/
theorem flat_torsion_of_isFinite (n : ℕ)
    [IsFinite (DefinitionsTorsion.Construction.torsionScheme A n).hom] : Flat (DefinitionsTorsion.Construction.torsionScheme A n).hom := by
  have : IsFinite (Multiplication.Construction.multiplicationMap A n).left :=
    Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A n
  exact MorphismProperty.of_isPullback (FinitePresentation.Construction.torsion_isPullback A n)
    (flat_multiplication_of_isFinite A n)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationFlat.Construction
