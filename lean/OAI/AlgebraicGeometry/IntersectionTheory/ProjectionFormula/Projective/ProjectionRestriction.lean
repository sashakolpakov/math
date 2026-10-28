import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-! # Projection Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction

noncomputable section

/-! Restricting the constructed projective projection to a closed
subscheme avoiding its center gives an actual proper morphism, with
the expected homogeneous coordinate preimages. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
  {X : Scheme} (i : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (hi : ∀ x, i x ∈ BasicOpen.RationalProjection.domain f)

def lift : X ⟶ (BasicOpen.RationalProjection.domain f).toScheme :=
  IsOpenImmersion.lift (BasicOpen.RationalProjection.domain f).ι i (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hi x)

theorem lift_fac : ProjectionRestriction.lift f i hi ≫ (BasicOpen.RationalProjection.domain f).ι = i := IsOpenImmersion.lift_fac _ _ _

def projection : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m := ProjectionRestriction.lift f i hi ≫ BasicOpen.RationalProjection.map f

theorem over_base (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z) :
    projection f i hi ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  rw [projection, Category.assoc, BasicOpen.RationalProjection.over_base f hC,
    ← Category.assoc, ProjectionRestriction.lift_fac]

theorem preimage_basicOpen (t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {e : ℕ}
    (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (he : 0 < e) :
    projection f i hi ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t =
      i ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t) := by
  change ProjectionRestriction.lift f i hi ⁻¹ᵁ (BasicOpen.RationalProjection.map f ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t) = _
  rw [BasicOpen.Projection.preimage_basicOpen f t ht he]
  ext x
  exact (congrArg (fun k => k x ∈ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t)) (ProjectionRestriction.lift_fac f i hi)).to_iff

theorem isProper [IsClosedImmersion i]
    (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z) : IsProper (projection f i hi) := by
  have hcomp : IsProper (projection f i hi ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) := by
    rw [over_base f i hi hC]
    infer_instance
  exact @IsProper.of_comp X (Foundations.Scheme.ProjectiveSpace.projectiveSpace m) Foundations.Scheme.ProjectiveSpace.complexBase (projection f i hi)
    (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) hcomp inferInstance

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction
