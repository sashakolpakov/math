import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.CohomologyNaturality

/-! # Cech Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechNaturality.IntrinsicCech

noncomputable section

/-! The positive-degree affine-cover comparison is natural for actual morphisms of quasicoherent module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u

theorem quasicoherent_affineCover_cechCohomologyIso_naturality
    {X : Scheme.{u}} [X.IsSeparated] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom)
        (n + 1) ≫ (CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso N U hU haffine n).hom =
      (CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso M U hU haffine n).hom ≫
        (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X (n + 1)).map f :=
  Cech.CohomologyNaturality.IntrinsicCech.cechHomologySuccIsoOfAcyclicIntersections_naturality U
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) hU
    (Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic M U haffine)
    (Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic N U haffine) n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechNaturality.IntrinsicCech
