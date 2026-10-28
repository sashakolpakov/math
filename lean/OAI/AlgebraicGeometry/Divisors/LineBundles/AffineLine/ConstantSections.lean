import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointFamily
import OAI.AlgebraicGeometry.Divisors.LineBundles.ComplexAffinePointCoordinate

/-! # Constant Sections -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ConstantSections.BundleCycles

noncomputable section

section

/-! The continuous affine-line family has the original base point and
the exact polynomial-evaluation coordinate under the scheme morphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory

def affineLineParameterOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) : OverProduct.BundleCycles.affineLineOver X ⟶ OverProduct.BundleCycles.complexAffineLineOver :=
  Over.homMk (AffineSpace.map PUnit X.hom) (AffineSpace.map_over X.hom)

theorem affineLineProductOverIso_snd (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (OverProduct.BundleCycles.affineLineProductOverIso X).hom ≫ snd X OverProduct.BundleCycles.complexAffineLineOver = affineLineParameterOver X :=
  Over.OverMorphism.ext (OverProduct.BundleCycles.affineLineProductSchemeIso_snd X)

theorem affineLinePointFamily_parameter (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ℂ) :
    PointFamily.BundleCycles.affineLinePointFamily X z ≫ affineLineParameterOver X = ComplexAffinePoints.BundleCycles.complexAffineLinePoint z.2 := by
  change (lift z.1 (ComplexAffinePoints.BundleCycles.complexAffineLinePoint z.2) ≫ (OverProduct.BundleCycles.affineLineProductOverIso X).inv) ≫ _ = _
  rw [← affineLineProductOverIso_snd, Category.assoc, Iso.inv_hom_id_assoc, lift_snd]

theorem affineLinePointFamily_coordinate (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ℂ) :
    (PointFamily.BundleCycles.affineLinePointFamily X z).left.appTop (Space.BundleCycles.affineLineCoordinate X.left) =
      (Scheme.ΓSpecIso (.of ℂ)).inv z.2 := by
  have h := congrArg (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints OverProduct.BundleCycles.complexAffineLineOver =>
    q.left.appTop (Space.BundleCycles.affineLineCoordinate Foundations.Scheme.ProjectiveSpace.complexBase)) (affineLinePointFamily_parameter X z)
  change (PointFamily.BundleCycles.affineLinePointFamily X z).left.appTop
    ((AffineSpace.map PUnit X.hom).appTop (AffineSpace.coord Foundations.Scheme.ProjectiveSpace.complexBase PUnit.unit)) = _ at h
  rw [AffineSpace.map_appTop_coord] at h
  exact h.trans (ComplexAffinePointCoordinate.BundleCycles.complexAffineLinePoint_coordinate z.2)

end

/-! Actual algebraic constant sections of the relative affine line,
identified with the continuous point family by base and coordinate. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def complexScalarSection (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) : Γ(X.left, ⊤) :=
  X.hom.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv a)

def affineLineConstantSection (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) : X.left ⟶ Charts.BundleCycles.affineLine X.left :=
  AffineSpace.homOfVector (𝟙 X.left) (fun _ : PUnit => complexScalarSection X a)

theorem affineLineConstantSection_over (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) :
    affineLineConstantSection X a ≫ Charts.BundleCycles.affineLineProjection X.left = 𝟙 X.left :=
  AffineSpace.homOfVector_over _ _

theorem affineLineConstantSection_coordinate (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) :
    (affineLineConstantSection X a).appTop (Space.BundleCycles.affineLineCoordinate X.left) = complexScalarSection X a :=
  AffineSpace.homOfVector_appTop_coord _ _ _

def affineLineConstantSectionOver (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ) : X ⟶ OverProduct.BundleCycles.affineLineOver X :=
  Over.homMk (affineLineConstantSection X a) (by
    change affineLineConstantSection X a ≫ (Charts.BundleCycles.affineLineProjection X.left ≫ X.hom) = X.hom
    rw [← Category.assoc, affineLineConstantSection_over, Category.id_comp])

theorem affineLineConstantSection_point_coordinate (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (x ≫ affineLineConstantSectionOver X a).left.appTop (Space.BundleCycles.affineLineCoordinate X.left) =
      (Scheme.ΓSpecIso (.of ℂ)).inv a := by
  change x.left.appTop ((affineLineConstantSection X a).appTop (Space.BundleCycles.affineLineCoordinate X.left)) = _
  rw [affineLineConstantSection_coordinate]
  exact congrArg (fun f => f.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv a)) x.w

theorem affineLinePointFamily_eq_constantSection (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (a : ℂ)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : PointFamily.BundleCycles.affineLinePointFamily X (x, a) = x ≫ affineLineConstantSectionOver X a := by
  apply Over.OverMorphism.ext
  apply AffineSpace.hom_ext
  · have h := congrArg (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => q.left) (PointFamily.BundleCycles.affineLinePointFamily_projection X (x, a))
    change (PointFamily.BundleCycles.affineLinePointFamily X (x, a)).left ≫ Charts.BundleCycles.affineLineProjection X.left = x.left at h
    change (PointFamily.BundleCycles.affineLinePointFamily X (x, a)).left ≫ Charts.BundleCycles.affineLineProjection X.left =
      (x.left ≫ affineLineConstantSection X a) ≫ Charts.BundleCycles.affineLineProjection X.left
    rw [Category.assoc, affineLineConstantSection_over, Category.comp_id]
    exact h
  · intro i
    cases i
    exact (affineLinePointFamily_coordinate X (x, a)).trans
      (affineLineConstantSection_point_coordinate X a x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ConstantSections.BundleCycles
