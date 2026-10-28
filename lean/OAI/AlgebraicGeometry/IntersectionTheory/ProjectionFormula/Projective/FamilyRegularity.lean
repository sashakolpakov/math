import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ClosedSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.StalkDimension

/-! # Family Regularity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity

noncomputable section

section

/-! The moving integral subscheme model is exactly the prescribed
closed support family, with its actual flat parameter morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace IntegralFamilySupport

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Polynomial.ProjectiveSubschemeFamily

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

def parameterLine : MatrixFamily.Family.space A ⟶ Spec (.of ℂ[X]) :=
  Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n ≫ Parameter.Polynomial.IntegralProduct.toLine A

instance flat_ambient : Flat (parameterLine A) := by
  let : Flat (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n) :=
    MorphismProperty.of_isPullback
      (Relative.ProjectivePullback.isPullback (FamilySupport.Family.coefficients A) n)
      inferInstance
  unfold parameterLine
  infer_instance

variable {Z : Scheme} [IsIntegral Z] [IsLocallyNoetherian Z]
  (i : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) [IsClosedImmersion i]

def support : IrreducibleCloseds (MatrixFamily.Family.space A) :=
  Closed.ImmersionSupport.support (Parameter.Polynomial.ProjectiveSubschemeFamily.moving A i)

theorem support_eq : (support A i : Set (MatrixFamily.Family.space A)) =
    (FamilySupport.Family.support A
      ⟨(Closed.ImmersionSupport.support i : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)),
        (Closed.ImmersionSupport.support i).isClosed⟩ :
          Set (MatrixFamily.Family.space A)) := by
  rw [support, ProjectionFormula.Flat.ClosedSupport.support_range]
  change Set.range ((MatrixFamily.Family.automorphism A).hom ∘ Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A i) =
    (MatrixFamily.Family.automorphism A).inv ⁻¹'
      (FamilySupport.Family.projection A ⁻¹'
        (Closed.ImmersionSupport.support i : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)))
  rw [Set.range_comp, FamilySupport.Family.inverse_preimage,
    ProjectionFormula.Flat.ClosedSupport.support_range]
  exact congrArg ((MatrixFamily.Family.automorphism A).hom '' ·)
    (Scheme.Pullback.range_fst (FamilySupport.Family.projection A) i)

instance flat_moving : Flat (Parameter.Polynomial.ProjectiveSubschemeFamily.moving A i ≫ parameterLine A) := by
  rw [parameterLine, ← Category.assoc, Parameter.Polynomial.ProjectiveSubschemeFamily.moving_parameter]
  infer_instance

instance flat_support : Flat (CycleClass.Geometric.GenericPoint.reducedSupportι (support A i) ≫ parameterLine A) :=
  ProjectionFormula.Flat.ClosedSupport.flat (Parameter.Polynomial.ProjectiveSubschemeFamily.moving A i) (parameterLine A)

end IntegralFamilySupport

end

/-! The actual matrix-family ambient scheme is integral and smooth
of total dimension n+1, giving native finite projective resolutions at its stalks. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

instance parameterDimension :
    SmoothOfRelativeDimension 1 (Parameter.Polynomial.IntegralProduct.parameterBase A) := by
  rw [← Parameter.Polynomial.IntegralProduct.over_base]
  exact smoothOfRelativeDimension_comp (Parameter.Polynomial.IntegralProduct.toLine A)
    Parameter.Polynomial.Line.base (n := 0) (m := 1)

instance relativeDimension :
    SmoothOfRelativeDimension n (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let : SmoothOfRelativeDimension n (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) :=
    Dimension.projective_relativeDimension n
  exact MorphismProperty.of_isPullback
    (Relative.ProjectivePullback.isPullback (FamilySupport.Family.coefficients A) n)
    (inferInstanceAs (SmoothOfRelativeDimension n (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))

def base : MatrixFamily.Family.space A ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n ≫ Parameter.Polynomial.IntegralProduct.parameterBase A

instance totalDimension : SmoothOfRelativeDimension (n + 1) (base A) :=
  smoothOfRelativeDimension_comp (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n)
    (Parameter.Polynomial.IntegralProduct.parameterBase A) (n := n) (m := 1)

instance integral : IsIntegral (MatrixFamily.Family.space A) := by
  let : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := Dimension.projective_integral n
  let : IsIso (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))) :=
    inferInstanceAs (IsIso (pullback.fst (FamilySupport.Family.projection A) (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))))
  exact IsIntegral.of_isIso (Parameter.Polynomial.ProjectiveSubschemeFamily.toAmbient A (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)))

theorem stalk_bound (x : MatrixFamily.Family.space A) :
    Polynomial.DimensionBound.GlobalBound ((MatrixFamily.Family.space A).presheaf.stalk x) (n + 1) :=
  Smooth.StalkDimension.stalk_bound (base A) (n + 1) x

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity
