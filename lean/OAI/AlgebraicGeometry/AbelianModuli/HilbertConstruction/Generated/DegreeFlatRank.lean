import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.DegreeFinitePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeDetermination

/-! # Degree Flat Rank -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A finite flatness and rank test on one generating quotient is equivalent to all generated finite quotient data. -/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} [Finite σ] {B N : ℕ} {r : ℕ → ℕ}

def Generated.DegreeFlatRank.GeneratedDegreeFlatRank
    (Q : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R N) (r N)) : Prop :=
  ∀ d : Fin (B + 1),
    Module.Flat R (MvPolynomial.homogeneousSubmodule σ R d ⧸ Single.DegreeRelationExtension.singleDegreePiece N Q.toSubmodule d) ∧
    ∀ p, Module.rankAtStalk (R := R)
      (MvPolynomial.homogeneousSubmodule σ R d ⧸ Single.DegreeRelationExtension.singleDegreePiece N Q.toSubmodule d) p = r d

variable (Q : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R N) (r N))
variable (hQ : Generated.DegreeFlatRank.GeneratedDegreeFlatRank (B := B) Q)

def Generated.DegreeFlatRank.generatedDegreeQuotient (d : Fin (B + 1)) :
    Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) (r d) := by
  letI := Single.DegreeFinitePresentation.singleDegreeQuotient_finitePresentation N Q.toSubmodule
    (Single.DegreeFinitePresentation.homogeneousGrassmannian_relations_fg N Q) d
  letI := (hQ d).1
  exact
    { toSubmodule := Single.DegreeRelationExtension.singleDegreePiece N Q.toSubmodule d
      finite_quotient := inferInstance
      projective_quotient := Module.Flat.projective_of_finitePresentation
      rankAtStalk_eq := (hQ d).2 }

def Generated.DegreeFlatRank.generatedDegreeData : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r where
  quotient := Generated.DegreeFlatRank.generatedDegreeQuotient Q hQ
  variable_mul d i := (Single.DegreeRelationExtension.singleDegreeRelations N Q.toSubmodule).variable_mul d i

theorem Generated.DegreeFlatRank.generatedDegreeData_generated : (Generated.DegreeFlatRank.generatedDegreeData Q hQ).GeneratedFromDegree N :=
  ⟨fun d hd => Single.DegreeRelationExtension.singleDegreePiece_below N Q.toSubmodule d hd,
    fun d hd => Single.DegreeRelationExtension.singleDegreePiece_succ N Q.toSubmodule d hd⟩

theorem Generated.DegreeFlatRank.generatedDegreeData_at (hN : N ≤ B) :
    (Generated.DegreeFlatRank.generatedDegreeData Q hQ).quotient ⟨N, Nat.lt_succ_of_le hN⟩ = Q := by
  apply Module.Grassmannian.ext
  exact Single.DegreeRelationExtension.singleDegreePiece_at N Q.toSubmodule

variable {Q hQ}

omit [Finite σ] in
theorem Truncated.GradedClassification.TruncatedGradedQuotientData.singleDegreePiece_eq_retained
    (D : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r) (hN : N ≤ B)
    (hD : D.GeneratedFromDegree N) (d : Fin (B + 1)) :
    Single.DegreeRelationExtension.singleDegreePiece N (D.quotient ⟨N, Nat.lt_succ_of_le hN⟩).toSubmodule d =
      (D.quotient d).toSubmodule :=
  (Single.DegreeIdealRelations.singleDegreePiece_eq_relations N _ D.generatedIdeal
    (D.generatedIdeal_span_degree N hN hD) d).trans (D.generatedIdeal_degree d)

omit [Finite σ] in
theorem Truncated.GradedClassification.TruncatedGradedQuotientData.generatingQuotient_flatRank
    (D : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r) (hN : N ≤ B)
    (hD : D.GeneratedFromDegree N) :
    Generated.DegreeFlatRank.GeneratedDegreeFlatRank (B := B) (D.quotient ⟨N, Nat.lt_succ_of_le hN⟩) := by
  intro d
  rw [D.singleDegreePiece_eq_retained hN hD d]
  exact ⟨inferInstance, (D.quotient d).rankAtStalk_eq⟩

def Generated.DegreeFlatRank.generatedDegreeFlatRankEquiv (hN : N ≤ B) :
    {D : Truncated.GradedClassification.TruncatedGradedQuotientData R σ B r // D.GeneratedFromDegree N} ≃
      {Q : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R N) (r N) //
        Generated.DegreeFlatRank.GeneratedDegreeFlatRank (B := B) Q} where
  toFun D := ⟨D.val.quotient ⟨N, Nat.lt_succ_of_le hN⟩,
    D.val.generatingQuotient_flatRank hN D.property⟩
  invFun Q := ⟨Generated.DegreeFlatRank.generatedDegreeData Q.val Q.property, Generated.DegreeFlatRank.generatedDegreeData_generated Q.val Q.property⟩
  left_inv D := Subtype.ext (Truncated.GradedClassification.TruncatedGradedQuotientData.eq_of_generating_quotient_eq _ _ hN
    (Generated.DegreeFlatRank.generatedDegreeData_generated _ _) D.property (Generated.DegreeFlatRank.generatedDegreeData_at _ _ hN))
  right_inv Q := Subtype.ext (Generated.DegreeFlatRank.generatedDegreeData_at Q.val Q.property hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
