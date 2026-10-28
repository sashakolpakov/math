import OAI.AlgebraicGeometry.SheafCohomology.AffineComparison

/-! # Scalars -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Scalars.Projective

noncomputable section

/-! The canonical complex scalar action on underlying Zariski cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Restrict the canonical global-functions action along the actual complex base map. -/
@[instance_reducible]
def zariskiComplexCohomologyModule (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (n : ℕ) : Module ℂ (AffineH.Projective.H M n) := by
  letI := AffineH.Projective.globalSectionsCohomologyModule M n
  exact Module.compHom (AffineH.Projective.H M n) (Sheaves.Projective.complexGlobalScalars A)

/-- Forgetting a complex scalar endomorphism gives multiplication by the
corresponding actual global regular function. -/
theorem forgetComplexScalarHom (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) (r : ℂ) :
    (IntegerCoefficients.Projective.integerSheafForget (TopCat.of A.carrier)).map
      ((Coefficients.Projective.restrictComplexSheaf (TopCat.of A.carrier)).map (r • 𝟙 (Sheaves.Projective.complexSheaf A M))) =
    (SheafOfModules.toSheaf A.carrier.ringCatSheaf).map
      (AffineH.Projective.globalSmulHom M (Sheaves.Projective.complexGlobalScalars A r)) := by
  apply Sheaf.hom_ext
  ext U x
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Scalars.Projective
