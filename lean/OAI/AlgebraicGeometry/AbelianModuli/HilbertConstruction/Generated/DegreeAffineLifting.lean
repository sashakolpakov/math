import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeFlatRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeProjection

/-! # Degree Affine Lifting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeAffineLifting

noncomputable section

/-! The single Grassmann projection has an exact affine lifting criterion in terms of finitely many actual degree quotients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ} (hN : N ≤ B)
variable (R : CommRingCat.{u}) (f : Spec R ⟶ S)

def generatedDegreeAffinePointEquiv :
    {Q : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N) (r N) //
      DegreeFlatRank.GeneratedDegreeFlatRank (B := B) Q} ≃
      (Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N) :=
  (DegreeFlatRank.generatedDegreeFlatRankEquiv hN).symm.trans (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f)

theorem generatedDegreeAffinePointEquiv_projection
    (Q : {Q : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N) (r N) //
      DegreeFlatRank.GeneratedDegreeFlatRank (B := B) Q}) :
    generatedDegreeAffinePointEquiv hN R f Q ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN =
      Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f Q.val := by
  change Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R f
    ⟨DegreeFlatRank.generatedDegreeData Q.val Q.property, DegreeFlatRank.generatedDegreeData_generated Q.val Q.property⟩ ≫
      (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N ≫
        Truncated.GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S ⟨N, Nat.lt_succ_of_le hN⟩) = _
  rw [← Category.assoc, Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv_inclusion,
    Truncated.GradedClassification.TruncatedGradedQuotientData.classifyingMap_projection, DegreeFlatRank.generatedDegreeData_at _ _ hN]

theorem generatedDegreeProjection_flatRank
    (x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N) :
    DegreeFlatRank.GeneratedDegreeFlatRank (B := B)
      ((Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f).symm
        (x ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN)) := by
  let j := Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N
  let d : Fin (B + 1) := ⟨N, Nat.lt_succ_of_le hN⟩
  let p := Truncated.GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S d
  have he : x ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN = (x ≫ j) ≫ p :=
    (Category.assoc x j p).symm
  rw [he]
  exact (Truncated.GradedRepresentation.truncatedGradedPointData (x ≫ j)).generatingQuotient_flatRank hN
    (Truncated.GeneratedParameters.truncatedGeneratedPoint_condition x)

theorem generatedDegreeProjection_affine_lift_iff
    (q : Over.mk f ⟶ Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) N (r N) S) :
    DegreeFlatRank.GeneratedDegreeFlatRank (B := B)
      ((Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f).symm q) ↔
      ∃! x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N,
        x ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN = q := by
  constructor
  · intro hq
    let Q := (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f).symm q
    let x := generatedDegreeAffinePointEquiv hN R f ⟨Q, hq⟩
    have hx : x ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN = q :=
      (generatedDegreeAffinePointEquiv_projection hN R f ⟨Q, hq⟩).trans
        ((Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f).apply_symm_apply q)
    exact ⟨x, hx, fun y hy => DegreeProjection.truncatedGeneratedDegreeProjection_affine_injective hN (hy.trans hx.symm)⟩
  · rintro ⟨x, hx, _⟩
    have h := generatedDegreeProjection_flatRank hN R f x
    rwa [hx] at h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeAffineLifting
