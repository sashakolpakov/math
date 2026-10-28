import OAI.AlgebraicGeometry.SheafCohomology.CechScalars

/-! # Cech Linear Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CechLinearComparison

noncomputable section

/-! Scalar compatibility of the actual affine-cover Čech comparison. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projective

universe u

/-- The affine-cover comparison respects the canonical global-functions actions
on both actual cohomology groups. -/
def affineCoverCechHSuccLinearEquiv {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := CechScalars.Projective.cechGlobalFunctionsModule M U (n + 1)
    letI := AffineH.Projective.globalSectionsCohomologyModule M (n + 1)
    (CechScalars.Projective.moduleCechCohomologyFunctor U (n + 1)).obj M ≃ₗ[Γ(X, ⊤)] AffineH.Projective.H M (n + 1) := by
  letI := CechScalars.Projective.cechGlobalFunctionsModule M U (n + 1)
  letI := AffineH.Projective.globalSectionsCohomologyModule M (n + 1)
  let e := (Cech.Projective.affineCoverCechHSuccIso M U hU hUaff n).addCommGroupIsoToAddEquiv
  refine { e with map_smul' := ?_ }
  intro r x
  have h := Cech.ComparisonNaturality.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections_naturality U
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (AffineH.Projective.globalSmulHom M r))
    hU.iSup_eq_top (Cech.Projective.affineCoverIntersectionsAcyclic M U hUaff)
    (Cech.Projective.affineCoverIntersectionsAcyclic M U hUaff) n
  exact ConcreteCategory.congr_hom h x

/-- Restricting the proven global-functions compatibility along the actual
complex structure map gives a complex-linear Čech comparison. -/
def cechHSuccLinearEquivZariski (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (M : A.carrier.Modules) [M.IsQuasicoherent]
    {ι : Type} (U : ι → A.carrier.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    letI := CechScalars.Projective.cechComplexCohomologyModule A M U (n + 1)
    letI := Scalars.Projective.zariskiComplexCohomologyModule A M (n + 1)
    (CechScalars.Projective.moduleCechCohomologyFunctor U (n + 1)).obj M ≃ₗ[ℂ] AffineH.Projective.H M (n + 1) := by
  have : A.carrier.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.variety.structureMap]
    infer_instance
  letI := CechScalars.Projective.cechGlobalFunctionsModule M U (n + 1)
  letI := AffineH.Projective.globalSectionsCohomologyModule M (n + 1)
  let e := affineCoverCechHSuccLinearEquiv M U hU hUaff n
  letI := CechScalars.Projective.cechComplexCohomologyModule A M U (n + 1)
  letI := Scalars.Projective.zariskiComplexCohomologyModule A M (n + 1)
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r x
  exact e.map_smul (Sheaves.Projective.complexGlobalScalars A r) x

/-- The actual ProjectiveCohomology cohomology is complex-linearly equivalent to native Čech
cohomology for the chosen finite affine cover. -/
def coherentHSuccLinearEquivCech (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) (n : ℕ) :
    letI := CechScalars.Projective.cechComplexCohomologyModule A L.sheaf (CechFiniteCover.Projective.finiteAffineCoverOpen A) (n + 1)
    Sheaves.Projective.coherentCohomology A L.sheaf (n + 1) ≃ₗ[ℂ]
      (CechScalars.Projective.moduleCechCohomologyFunctor (CechFiniteCover.Projective.finiteAffineCoverOpen A) (n + 1)).obj L.sheaf := by
  have : L.sheaf.IsQuasicoherent :=
    (LineBundleLocalGenerators.Projective.lineBundleLocalGenerators A L).quasiCoherentData.isQuasicoherent
  letI := CechScalars.Projective.cechComplexCohomologyModule A L.sheaf (CechFiniteCover.Projective.finiteAffineCoverOpen A) (n + 1)
  letI := Scalars.Projective.zariskiComplexCohomologyModule A L.sheaf (n + 1)
  exact (LinearComparison.Projective.coherentCohomologyLinearEquivZariski A L.sheaf (n + 1)).trans
    (cechHSuccLinearEquivZariski A L.sheaf (CechFiniteCover.Projective.finiteAffineCoverOpen A)
      (CechFiniteCover.Projective.finiteAffineCoverOpen_covers A) (CechFiniteCover.Projective.finiteAffineCoverOpen_affine A) n).symm

/-- The comparison preserves the actual complex dimensions. -/
theorem coherentCohomology_finrank_eq_cech (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : Sheaves.Projective.LineBundle A) (n : ℕ) :
    letI := CechScalars.Projective.cechComplexCohomologyModule A L.sheaf (CechFiniteCover.Projective.finiteAffineCoverOpen A) (n + 1)
    Module.finrank ℂ (Sheaves.Projective.coherentCohomology A L.sheaf (n + 1)) =
      Module.finrank ℂ
        ((CechScalars.Projective.moduleCechCohomologyFunctor (CechFiniteCover.Projective.finiteAffineCoverOpen A) (n + 1)).obj L.sheaf) := by
  let := CechScalars.Projective.cechComplexCohomologyModule A L.sheaf (CechFiniteCover.Projective.finiteAffineCoverOpen A) (n + 1)
  exact (coherentHSuccLinearEquivCech A L n).finrank_eq

end Projective

end

end OAI.AlgebraicGeometry.SheafCohomology.CechLinearComparison
