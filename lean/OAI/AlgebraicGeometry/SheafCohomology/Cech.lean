import OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison
import OAI.AlgebraicGeometry.SheafCohomology.CechFiniteCover
import OAI.AlgebraicGeometry.SheafCohomology.LinearComparison

/-! # Cech -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.Projective

noncomputable section

/-! The actual finite affine cover computes ProjectiveCohomology cohomology in all positive degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

/-- Affine tuple intersections of a separated scheme satisfy the actual sheaf
acyclicity hypotheses of the Čech comparison. -/
theorem affineCoverIntersectionsAcyclic {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  intro p i q
  change Subsingleton (AffineH.Projective.H
    ((Scheme.Modules.restrictFunctor (∏ᶜ fun k : Fin (p + 1) => U (i k)).ι).obj M)
    (q + 1))
  exact CechAcyclicIntersections.Projective.affineIntersectionCohomology_vanish M U hUaff p q i

/-- The actual Čech complex of a quasicoherent sheaf on a separated scheme's
affine cover computes its Zariski cohomology in every positive degree. -/
def affineCoverCechHSuccIso {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    ((cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
  Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U _ hU.iSup_eq_top
    (affineCoverIntersectionsAcyclic M U hUaff) n

/-- ProjectiveCohomology's actual positive-degree cohomology is additively equivalent to the
Čech cohomology of its chosen finite affine cover. -/
def coherentHSuccAddEquivCech (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A) (n : ℕ) :
    Sheaves.Projective.coherentCohomology A L.sheaf (n + 1) ≃+
      ((cechComplexFunctor (CechFiniteCover.Projective.finiteAffineCoverOpen A)).obj
        ((SheafOfModules.toSheaf A.carrier.ringCatSheaf).obj L.sheaf).obj).homology (n + 1) := by
  have : A.carrier.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.variety.structureMap]
    infer_instance
  have : L.sheaf.IsQuasicoherent :=
    (LineBundleLocalGenerators.Projective.lineBundleLocalGenerators A L).quasiCoherentData.isQuasicoherent
  exact (LinearComparison.Projective.complexSheafCohomologyAddEquiv (TopCat.of A.carrier)
    (Sheaves.Projective.complexSheaf A L.sheaf) (n + 1)).trans
      (affineCoverCechHSuccIso L.sheaf (CechFiniteCover.Projective.finiteAffineCoverOpen A)
        (CechFiniteCover.Projective.finiteAffineCoverOpen_covers A) (CechFiniteCover.Projective.finiteAffineCoverOpen_affine A)
        n).symm.addCommGroupIsoToAddEquiv

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.Projective
