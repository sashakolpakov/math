import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.CoherentCohomology

/-! # Affine Coherent Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineCoherentCohomology

noncomputable section

/-! Proper coherent cohomology and global sections are finite over the actual ring of functions of any Noetherian affine base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem schemeCoefficientMap_toSpec_comp {X S : Scheme.{u}} (f : X ⟶ S) :
    Coefficient.ModulePresheaf.schemeCoefficientMap (f ≫ S.toSpecΓ) = f.appTop.hom := by
  ext r
  change f.appTop (S.toSpecΓ.appTop ((Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv r)) = f.appTop r
  rw [Scheme.toSpecΓ_appTop]
  exact congrArg f.appTop ((Scheme.ΓSpecIso (.of Γ(S, ⊤))).inv_hom_id_apply r)

theorem proper_coherent_cohomologyFinite_affine
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    CoefficientCohomology.FinitenessProperty.ZariskiCohomology.CoefficientCohomologyFinite f.appTop.hom M := by
  have h := CoherentCohomology.proper_coherent_cohomologyFinite (f ≫ S.toSpecΓ) M
  intro n
  have := h n
  exact Module.Finite.equiv
    (CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr (schemeCoefficientMap_toSpec_comp f) M n).toLinearEquiv

theorem proper_coherent_globalSections_finite
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor f.appTop.hom).obj M) := by
  have := proper_coherent_cohomologyFinite_affine f M 0
  exact Module.Finite.equiv (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv f.appTop.hom M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AffineCoherentCohomology
