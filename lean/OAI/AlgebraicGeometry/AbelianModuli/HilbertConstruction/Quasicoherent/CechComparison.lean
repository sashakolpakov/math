import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicCech.SheafCohomologyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity

/-! # Cech Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech

noncomputable section

/-! Every affine open cover of a separated scheme computes the positive genuine Zariski cohomology of a quasicoherent module by the native Čech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

def quasicoherent_affineCover_cechCohomologyIso
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    ((cechComplexFunctor U).obj M.presheaf).homology (n + 1) ≅
      (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (n + 1)).obj M :=
  IntrinsicCech.SheafCohomologyComparison.cechHomologySuccIsoOfAcyclicIntersections U
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hU
    (Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M U haffine) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech
