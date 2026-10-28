import OAI.AlgebraicGeometry.SheafCohomology.Cech.Cochains
import OAI.AlgebraicGeometry.SheafCohomology.ProjectiveAffineVanishing

/-! # Cech Acyclic Intersections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CechAcyclicIntersections.Projective

noncomputable section

/-! Actual quasicoherent cohomology vanishes on the intersections in an affine cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

/-- All nonempty tuple intersections in an affine cover of a separated scheme
are acyclic for quasicoherent Zariski cohomology. -/
theorem affineIntersectionCohomology_vanish
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (n q : ℕ) (i : Fin (n + 1) → ι) :
    Subsingleton (AffineH.Projective.H
      ((Scheme.Modules.restrictFunctor (∏ᶜ fun k : Fin (n + 1) => U (i k)).ι).obj M)
      (q + 1)) := by
  have : IsAffine (∏ᶜ fun k : Fin (n + 1) => U (i k)).toScheme :=
    Cech.Cochains.IsAffineOpen.cechIntersection U hU n i
  exact AffineVanishing.Projective.moduleAffineHSucc_subsingleton _ q

/-- The acyclicity applies to the actual sheaf of any ProjectiveCohomology line bundle. -/
theorem lineBundleAffineIntersectionCohomology_vanish
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : Sheaves.Projective.LineBundle A)
    {ι : Type} (U : ι → A.carrier.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (n q : ℕ) (i : Fin (n + 1) → ι) :
    Subsingleton (AffineH.Projective.H
      ((Scheme.Modules.restrictFunctor (∏ᶜ fun k : Fin (n + 1) => U (i k)).ι).obj L.sheaf)
      (q + 1)) := by
  have : A.carrier.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.variety.structureMap]
    infer_instance
  have : L.sheaf.IsQuasicoherent :=
    (LineBundleLocalGenerators.Projective.lineBundleLocalGenerators A L).quasiCoherentData.isQuasicoherent
  exact affineIntersectionCohomology_vanish L.sheaf U hU n q i

end

end OAI.AlgebraicGeometry.SheafCohomology.CechAcyclicIntersections.Projective
