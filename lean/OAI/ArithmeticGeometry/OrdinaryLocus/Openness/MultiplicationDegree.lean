import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.EmbeddedMultiplicationHilbertPolynomials
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatProjectiveDegree
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationRank

/-! # Multiplication Degree -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree.Construction

noncomputable section

/-! The unconditional total-degree formula for multiplication on a smooth proper connected geometric group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

theorem multiplication_finrank_eq_power_dimension
    {K : Type} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (m : ℕ) (hm : 0 < m) [IsFinite (DefinitionsTorsion.Construction.torsionScheme A m).hom]
    (g : ℕ) (hdim : topologicalKrullDim A.left = (g : WithBot ℕ∞)) (x : A.left) :
    (Multiplication.Construction.multiplicationMap A m).left.finrank x = m ^ (2 * g) := by
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  let f := (Multiplication.Construction.multiplicationMap A m).left
  have : IsFinite f := Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A m
  obtain ⟨hsurj, hflat⟩ := FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A m
  have : Surjective f := hsurj
  have : Flat f := hflat
  obtain ⟨L, hL, hs⟩ := GroupAmpleBundle.Construction.exists_symmetric_ample_lineBundle A
  let R := Γ(Spec (.of K), ⊤)
  let : Field R := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField K
  let : Field Γ(Spec (.of R), ⊤) := AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint.Construction.FieldPointPrime.sectionsField R
  obtain ⟨d, hd, r, a, ha, hb, ⟨e⟩⟩ := AmpleEmbeddingPower.Construction.ample_exists_closed_embedding_power A.hom L hL
  have : IsClosedImmersion a := ha
  obtain ⟨P, Q, b, hPne, hdeg, hP, hQ, hscale⟩ :=
    EmbeddedMultiplicationHilbertPolynomials.Construction.embedded_multiplication_Hilbert_polynomials A L hL hs m hm d r hd a hb e
  obtain ⟨z, hz⟩ := FiniteFlatProjectiveDegree.Construction.finiteFlat_projective_rank_of_rescaling (Field.toIsField _) f a 0
    P Q hPne b hP hQ (m ^ 2) (pow_pos hm 2) hscale
  have hnat : P.natDegree = g := by exact_mod_cast hdeg.trans hdim
  have hz' : f.finrank z = m ^ (2 * g) := by
    simpa only [hnat, ← pow_mul] using hz
  exact (MultiplicationRank.Construction.multiplication_finrank_eq A m x z).trans hz'

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDegree.Construction
