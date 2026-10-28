import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DegreeReduction
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree

/-! # Open -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.OrdinaryLocus.Openness.Open.Construction

/-! Openness of the ordinary locus under the exact hypotheses of Statements.Openness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem isOpen_ordinaryLocus
    (p : ℕ) [Fact p.Prime]
    (S : Over (Spec (CommRingCat.of (ZMod p))))
    (A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    IsOpen {s : S.left | DefinitionsTorsion.IsOrdinaryAt p A s} := by
  apply DegreeReduction.Construction.isOpen_ordinaryLocus_of_multiplication_degree p ?_ S A
  intro k _ _ _ B _ _ _ _ _ _ g hg b
  exact MultiplicationDegree.Construction.multiplication_finrank_eq_power_dimension B p (Fact.out : p.Prime).pos g hg b

end ArithmeticGeometry.OrdinaryLocus.Openness.Open.Construction

namespace ArithmeticGeometry.OrdinaryLocus.Openness.Open

/-! The Openness statement, with its proof supplied by the completed development. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- Openness: the ordinary locus of an abelian scheme is Zariski open. -/
theorem isOpen_ordinaryLocus
    (p : ℕ) [Fact p.Prime]
    (S : Over (Spec (CommRingCat.of (ZMod p))))
    (A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    IsOpen {s : S.left | DefinitionsTorsion.IsOrdinaryAt p A s} := by
  exact Construction.isOpen_ordinaryLocus p S A

end ArithmeticGeometry.OrdinaryLocus.Openness.Open

end

end OAI
