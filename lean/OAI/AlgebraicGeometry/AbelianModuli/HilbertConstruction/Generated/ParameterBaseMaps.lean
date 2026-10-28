import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ParameterBaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ClassifierProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.MonoRecognition

/-! # Parameter Base Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterBaseMaps

noncomputable section

/-! Changing the base scheme gives a unique actual map between generated parameter schemes, compatible with their generating-degree Grassmann maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ) (hN : N ≤ B)

def generatedAmbientBaseMap :
    (Over.map f).obj (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N) ⟶
      Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) N (r N) S :=
  (Over.map f).map (DegreeProjection.truncatedGeneratedDegreeProjection T n B r N hN) ≫
    Homogeneous.ParameterBaseMaps.homogeneousParameterBaseMapOver f n N (r N)

theorem generatedParameterBaseMap_existsUnique :
    ∃! g : (Over.map f).obj (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N) ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N,
      g ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN = generatedAmbientBaseMap f n B r N hN := by
  apply Affine.MonoRecognition.overMono_lift_of_affine
  intro R b a
  let t := a.left ≫ (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).hom
  let a' : Over.mk t ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N := Over.homMk a.left rfl
  let D := (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R t).symm a'
  let U := D.val.quotient ⟨N, Nat.lt_succ_of_le hN⟩
  let y := Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R b D
  have ha : Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R t D = a' :=
    (Truncated.GeneratedParameters.truncatedGeneratedAffinePointEquiv R t).apply_symm_apply a'
  have hproj := ClassifierProjection.truncatedGeneratedClassifier_projection hN R t D
  rw [ha] at hproj
  have hp : a.left ≫ (DegreeProjection.truncatedGeneratedDegreeProjection T n B r N hN).left =
      (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R t U).left :=
    congrArg Over.Hom.left hproj
  have ht : t ≫ f = b := by
    change (a.left ≫ (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).hom) ≫ f = b
    rw [Category.assoc]
    exact a.w
  refine ⟨y, ?_⟩
  apply Over.OverMorphism.ext
  change y.left ≫ (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN).left =
    a.left ≫ ((DegreeProjection.truncatedGeneratedDegreeProjection T n B r N hN).left ≫ Homogeneous.ParameterBaseMaps.homogeneousParameterBaseMap f n N (r N))
  calc
    _ = (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R b U).left :=
      congrArg Over.Hom.left (ClassifierProjection.truncatedGeneratedClassifier_projection hN R b D)
    _ = (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R (t ≫ f) U).left := by rw [ht]
    _ = (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R t U).left ≫
        Homogeneous.ParameterBaseMaps.homogeneousParameterBaseMap f n N (r N) := (Homogeneous.ParameterBaseMaps.homogeneousQuotientClassifier_postcomp f n N (r N) R t U).symm
    _ = (a.left ≫ (DegreeProjection.truncatedGeneratedDegreeProjection T n B r N hN).left) ≫
        Homogeneous.ParameterBaseMaps.homogeneousParameterBaseMap f n N (r N) := congrArg (fun c => c ≫ Homogeneous.ParameterBaseMaps.homogeneousParameterBaseMap f n N (r N)) hp.symm
    _ = _ := Category.assoc _ _ _

def generatedParameterBaseMapOver :
    (Over.map f).obj (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N) ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N :=
  (generatedParameterBaseMap_existsUnique f n B r N hN).choose

def generatedParameterBaseMap :
    (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).left ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left :=
  (generatedParameterBaseMapOver f n B r N hN).left

theorem generatedParameterBaseMap_projection :
    generatedParameterBaseMap f n B r N hN ≫ (DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN).left =
      (DegreeProjection.truncatedGeneratedDegreeProjection T n B r N hN).left ≫ Homogeneous.ParameterBaseMaps.homogeneousParameterBaseMap f n N (r N) :=
  congrArg Over.Hom.left (generatedParameterBaseMap_existsUnique f n B r N hN).choose_spec.1

theorem generatedParameterBaseMap_over :
    generatedParameterBaseMap f n B r N hN ≫ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom =
      (Truncated.GeneratedParameters.truncatedGeneratedParameters T n B r N).hom ≫ f :=
  (generatedParameterBaseMapOver f n B r N hN).w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterBaseMaps
