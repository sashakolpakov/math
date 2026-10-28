import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleLocalization
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleSheaf

/-! # Exterior Restrictions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorRestrictions

noncomputable section

/-! On actual affine schemes, the exterior-form restriction to a basic open is localization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

abbrev globalCoordinateAlgebra : CommAlgCat.{0} ℂ :=
  (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).obj (op ⊤)

abbrev basicCoordinateAlgebra (r : globalCoordinateAlgebra X) : CommAlgCat.{0} ℂ :=
  (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).obj (op (X.left.basicOpen r))

def basicOpenRestriction (r : globalCoordinateAlgebra X) :
    (op (⊤ : X.left.Opens)) ⟶ op (X.left.basicOpen r) := (homOfLE le_top).op

theorem basicCoordinateAlgebra_isLocalization [IsAffine X.left] (r : globalCoordinateAlgebra X) :
    letI := ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map (basicOpenRestriction X r)).hom.toRingHom.toAlgebra
    IsLocalization (Submonoid.powers r) (basicCoordinateAlgebra X r) := by
  exact (isAffineOpen_top X.left).isLocalization_of_eq_basicOpen r (homOfLE le_top) rfl

def basicExteriorRestriction (r : globalCoordinateAlgebra X) (n : ℕ) :
    letI := ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map (basicOpenRestriction X r)).hom.toRingHom.toAlgebra
    Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (globalCoordinateAlgebra X) n →ₗ[globalCoordinateAlgebra X]
      Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (basicCoordinateAlgebra X r) n :=
  Exterior.ModuleLocalization.formModuleMapCoefficient (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X) (basicOpenRestriction X r) n

theorem basicExteriorRestriction_isLocalizedModule [IsAffine X.left]
    [Module.Free (globalCoordinateAlgebra X) Ω[globalCoordinateAlgebra X⁄ℂ]]
    (r : globalCoordinateAlgebra X) (n : ℕ) :
    letI := ((Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X).map (basicOpenRestriction X r)).hom.toRingHom.toAlgebra
    IsLocalizedModule (Submonoid.powers r) (basicExteriorRestriction X r n) :=
  Exterior.ModuleLocalization.formModuleMapCoefficient_isLocalizedModule (Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℂ X)
    (basicOpenRestriction X r) (Submonoid.powers r) (basicCoordinateAlgebra_isLocalization X r) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorRestrictions
