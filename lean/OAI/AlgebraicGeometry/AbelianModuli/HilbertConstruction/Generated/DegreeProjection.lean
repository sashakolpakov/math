import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeDetermination
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedParameters

/-! # Degree Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeProjection

noncomputable section

/-! The generated parameter scheme maps monomorphically to the single Grassmannian in its generating degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ) (hN : N ≤ B)

def truncatedGeneratedDegreeProjection : Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N ⟶
    Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) N (r N) S :=
  Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N ≫
    Truncated.GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S ⟨N, Nat.lt_succ_of_le hN⟩

variable {S n B r N}

theorem truncatedGeneratedDegreeProjection_affine_injective {R : CommRingCat.{u}} {f : Spec R ⟶ S} :
    Function.Injective (fun x : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N =>
      x ≫ truncatedGeneratedDegreeProjection S n B r N hN) := by
  intro x y h
  let d : Fin (B + 1) := ⟨N, Nat.lt_succ_of_le hN⟩
  let j := Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N
  let p := Truncated.GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S d
  change x ≫ (j ≫ p) = y ≫ (j ≫ p) at h
  have hp : (x ≫ j) ≫ p = (y ≫ j) ≫ p := by
    rw [Category.assoc, Category.assoc]
    exact h
  have hq : (Truncated.GradedRepresentation.truncatedGradedPointData (x ≫ Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N)).quotient
      ⟨N, Nat.lt_succ_of_le hN⟩ =
      (Truncated.GradedRepresentation.truncatedGradedPointData (y ≫ Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N)).quotient
        ⟨N, Nat.lt_succ_of_le hN⟩ := by
    exact congrArg (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0}
      (Fin (n + 1)) N (r N) R f).symm hp
  have hd := Truncated.GradedClassification.TruncatedGradedQuotientData.eq_of_generating_quotient_eq _ _ hN
    (Truncated.GeneratedParameters.truncatedGeneratedPoint_condition x) (Truncated.GeneratedParameters.truncatedGeneratedPoint_condition y) hq
  have he : x ≫ Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N =
      y ≫ Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N :=
    (Truncated.GradedRepresentation.truncatedGradedPointData_classifyingMap _).symm.trans
      ((congrArg (fun D => D.classifyingMap f) hd).trans (Truncated.GradedRepresentation.truncatedGradedPointData_classifyingMap _))
  have : Mono (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N) := Over.mono_of_mono_left _
  exact (cancel_mono (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N)).mp he

theorem truncatedGeneratedDegreeProjection_injective {T : Over S} :
    Function.Injective (fun x : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N =>
      x ≫ truncatedGeneratedDegreeProjection S n B r N hN) := by
  intro x y h
  change x ≫ truncatedGeneratedDegreeProjection S n B r N hN =
    y ≫ truncatedGeneratedDegreeProjection S n B r N hN at h
  apply Over.OverMorphism.ext
  apply T.left.affineOpenCover.openCover.hom_ext
  intro i
  change T.left.affineOpenCover.I₀ at i
  let a : Over.mk (T.left.affineOpenCover.f i ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.affineOpenCover.f i)
  have he : (a ≫ x) ≫ truncatedGeneratedDegreeProjection S n B r N hN =
      (a ≫ y) ≫ truncatedGeneratedDegreeProjection S n B r N hN := by
    rw [Category.assoc, Category.assoc, h]
  exact congrArg Over.Hom.left (truncatedGeneratedDegreeProjection_affine_injective hN he)

instance truncatedGeneratedDegreeProjection_mono :
    Mono (truncatedGeneratedDegreeProjection S n B r N hN) where
  right_cancellation _ _ h := truncatedGeneratedDegreeProjection_injective hN h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeProjection
