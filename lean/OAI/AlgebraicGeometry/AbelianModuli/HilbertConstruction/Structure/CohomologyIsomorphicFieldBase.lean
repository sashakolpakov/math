import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.IsomorphismCohomologyDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso

/-! # Cohomology Isomorphic Field Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.CohomologyIsomorphicFieldBase

noncomputable section

/-! Structure-sheaf cohomology dimensions are unchanged in an actual Cartesian square whose base map is an isomorphism of field spectra. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem structureCohomology_finrank_isomorphic_field_base
    {K B : Type u} [Field K] [Field B] {X Y : Scheme.{u}} [Y.IsSeparated]
    {a : X ⟶ Y} {b : X ⟶ Spec (.of B)} {p : Y ⟶ Spec (.of K)} {c : Spec (.of B) ⟶ Spec (.of K)}
    (H : IsPullback a b p c) [IsIso c] (q : ℕ) :
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj (Line.Bundles.structureModule Y)) =
      Module.finrank B ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap b) q).obj (Line.Bundles.structureModule X)) := by
  have : IsIso a := H.isIso_fst_of_isIso
  let eP := CohomologyPullbackIso.lineBundleCohomologyPullbackIso a p (Line.Bundles.LineBundle.trivial Y) q
  let eS := (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap (a ≫ p)) q).mapIso
    (Line.Bundles.structureModulePullbackIso a)
  have h₁ : Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).obj (Line.Bundles.structureModule Y)) =
      Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap (a ≫ p)) q).obj (Line.Bundles.structureModule X)) :=
    eP.toLinearEquiv.finrank_eq.symm.trans eS.toLinearEquiv.finrank_eq
  have h₂ := congrArg (fun t : X ⟶ Spec (.of K) =>
    Module.finrank K ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap t) q).obj
      (Line.Bundles.structureModule X))) H.w
  exact h₁.trans (h₂.trans (HilbertConstruction.Spec.IsomorphismCohomologyDimension.coefficientCohomology_finrank_specIso c b (Line.Bundles.structureModule X) q))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.CohomologyIsomorphicFieldBase
