import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.AcyclicIntersectionColumns
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CechIntersections

/-! # Cover Cech Acyclicity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech

noncomputable section

/-! Quasicoherence on a separated scheme supplies the actual acyclic-intersection hypothesis for every family of affine opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

theorem quasicoherent_affine_intersections_acyclic
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    Cech.AcyclicIntersectionColumns.IntrinsicCech.CechIntersectionsAcyclic U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
  intro p i q
  let V : X.Opens := ∏ᶜ fun k : Fin (p + 1) => U (i k)
  have : IsAffine V.toScheme := CechIntersections.affine_cechIntersection U hU p i
  change Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (M.restrict V.ι) (q + 1))
  exact ZariskiVanishing.ZariskiCohomology.moduleAffineHSucc_subsingleton (M.restrict V.ι) q

theorem quasicoherent_affine_cech_columns_exact
    {X : Scheme.{u}} [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (p q : ℕ) :
    ((Cech.InjectiveBicomplex.IntrinsicCech.cechInjectiveResolutionBicomplex U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).flip.X p).ExactAt (q + 1) :=
  Cech.AcyclicIntersectionColumns.IntrinsicCech.cechInjectiveResolution_columns_exactAt_succ U _
    (quasicoherent_affine_intersections_acyclic M U hU) p q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech
