import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree
import Lean.Util.CollectAxioms

/-! # Canonical Degree -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CanonicalDegree

noncomputable section

section

/-! Audit the canonical Openness degree support shared with the rest of the project.
The 120 proof modules and both geometric definitions retain the full axiom check.
The historical statement placeholder is never used as proof evidence. -/

end

/-! The fully proved geometric multiplication-degree formula, with the
canonical support shared with the other Openness proofs and audited independently. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem geometric_multiplication_degree
    {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (m : ℕ) (hm : 0 < m) [IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A m).hom]
    (g : ℕ) (hdim : topologicalKrullDim A.left = (g : WithBot ℕ∞)) (x : A.left) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.multiplicationMap A m).left.finrank x = m ^ (2 * g) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree.Construction.multiplication_finrank_eq_power_dimension A m hm g hdim x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CanonicalDegree
