import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteRationalPoints
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Reduction

/-! # Field Reduction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldReduction.Construction

noncomputable section

/-! Reduction of Openness to the finite p-torsion bound over algebraically closed fields. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

/-- The only field-level input needed by the openness argument is the
p-torsion bound for a finite kernel over an algebraically closed field.
All geometric base changes and the possibility of an infinite point set
are handled in this reduction. -/
theorem isOpen_ordinaryLocus_of_finite_field_bound
    (p : ℕ) [Fact p.Prime]
    (hfield : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharP K p]
      (B : Over (Spec (.of K))) [GrpObj B] [IsCommMonObj B]
      [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
      [IsFinite (DefinitionsTorsion.Construction.torsionScheme B p).hom] (g : ℕ),
      topologicalKrullDim B.left = (g : WithBot ℕ∞) →
      Nat.card {x : Over.mk (𝟙 (Spec (.of K))) ⟶ B // x ^ p = 1} ≤ p ^ g)
    (S : Over (Spec (.of (ZMod p))))
    (A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    IsOpen {s : S.left | DefinitionsTorsion.IsOrdinaryAt p A s} := by
  apply Reduction.Construction.isOpen_ordinaryLocus_of_torsionPointCard_bound A p
  intro s
  let K := AlgebraicClosure (S.left.residueField s)
  let t : Spec (.of K) ⟶ S.left := (DefinitionsTorsion.geometricPoint S.left s).hom
  let F := Over.pullback t
  let B := F.obj A
  have : CharP K p := GeometricTorsionPoints.Construction.charP_geometric_residueField p S s
  have : Smooth B.hom := by change Smooth (pullback.snd A.hom t); infer_instance
  have : IsProper B.hom := by change IsProper (pullback.snd A.hom t); infer_instance
  have : GeometricallyConnected B.hom := by
    change GeometricallyConnected (pullback.snd A.hom t)
    infer_instance
  have hcard := GeometricTorsionPoints.Construction.torsionPointCard_fieldBaseChange t A p
  change Nat.card {x : Over.mk (𝟙 (Spec (.of K))) ⟶ B // x ^ p = 1} =
    Nat.card {x : DefinitionsTorsion.geometricPoint S.left s ⟶ A // x ^ p = 1} at hcard
  by_cases hz : Nat.card {x : Over.mk (𝟙 (Spec (.of K))) ⟶ B // x ^ p = 1} = 0
  · rw [← hcard, hz]
    exact Nat.zero_le _
  have : Finite {x : Over.mk (𝟙 (Spec (.of K))) ⟶ B // x ^ p = 1} :=
    Nat.finite_of_card_ne_zero hz
  have : Finite (Over.mk (𝟙 (Spec (.of K))) ⟶ DefinitionsTorsion.Construction.torsionScheme B p) :=
    Finite.of_equiv _ (DefinitionsTorsion.Construction.torsionPointsEquiv B p (Over.mk (𝟙 (Spec (.of K))))).symm
  have : IsFinite (DefinitionsTorsion.Construction.torsionScheme B p).hom :=
    FiniteRationalPoints.Construction.isFinite_of_proper_of_finite_rationalPoints (DefinitionsTorsion.Construction.torsionScheme B p)
  have hdim : topologicalKrullDim B.left = (FiberDimension.Construction.fiberDimension A s : WithBot ℕ∞) :=
    (GeometricDimension.Construction.topologicalKrullDim_geometricFiber A s).trans (FiberDimension.Construction.fiberDimension_spec A s)
  exact hcard.symm.trans_le (hfield K B (FiberDimension.Construction.fiberDimension A s) hdim)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldReduction.Construction
