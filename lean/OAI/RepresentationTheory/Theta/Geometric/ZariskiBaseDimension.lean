import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.LinearComparison
import Mathlib.Algebra.Field.Equiv

/-! # Zariski Base Dimension -/

namespace OAI.RepresentationTheory.Theta.Geometric.ZariskiBaseDimension

noncomputable section

/-! Changing from the literal global functions on Spec C to C preserves
the dimension of the original algebraic sheaf cohomology module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem zariskiBase_finrank_complex (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) (q : ℕ) :
    letI := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
    letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A M q
    Module.finrank Γ(AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q) =
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q) := by
  let := AlgebraicGeometry.SheafCohomology.AffineH.Projective.globalSectionsCohomologyModule M q
  let := AlgebraicGeometry.SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule A.variety.structureMap M q
  let := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A M q
  let e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  have h := _root_.rank_eq_of_equiv_equiv e (AddEquiv.refl (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M q)) e.bijective (by
    intro r x
    change A.variety.structureMap.appTop r • x =
      A.variety.structureMap.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r)) • x
    rw [Iso.hom_inv_id_apply])
  exact congrArg Cardinal.toNat h

end

end OAI.RepresentationTheory.Theta.Geometric.ZariskiBaseDimension
