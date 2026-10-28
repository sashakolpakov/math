import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeAbelianCohomology
import OAI.AlgebraicGeometry.SheafCohomology.Cech.Comparison

/-! # Affine Cohomology Comparison -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCohomologyComparison.Construction

noncomputable section

/-! The checked affine acyclicity and Cech-to-sheaf comparison applied to actual Openness modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem quasicoherent_affine_H_succ_subsingleton {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((SchemeAbelianCohomology.Construction.schemeModulesToAbelian X).obj M) (n + 1)) :=
  AlgebraicGeometry.SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton M n

theorem quasicoherent_affineCover_acyclic {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    AlgebraicGeometry.SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic U ((SchemeAbelianCohomology.Construction.schemeModulesToAbelian X).obj M) := by
  intro p i n
  have : IsAffine (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).toScheme :=
    AlgebraicGeometry.SheafCohomology.Cech.Cochains.IsAffineOpen.cechIntersection U hU p i
  change Subsingleton (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H
    ((Scheme.Modules.restrictFunctor (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)).ι).obj M) (n + 1))
  exact AlgebraicGeometry.SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton _ n

def quasicoherent_affineCechHomologyIso {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    ((cechComplexFunctor U).obj ((SchemeAbelianCohomology.Construction.schemeModulesToAbelian X).obj M).obj).homology (n + 1) ≅
      (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) (n + 1)).obj
        ((SchemeAbelianCohomology.Construction.schemeModulesToAbelian X).obj M) :=
  AlgebraicGeometry.SheafCohomology.Cech.Comparison.TopCat.Sheaf.cechHomologySuccIsoOfAcyclicIntersections U _ hcover
    (quasicoherent_affineCover_acyclic M U hU) n

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineCohomologyComparison.Construction
