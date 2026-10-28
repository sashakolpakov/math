import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldCohomology

/-! # Residue Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every positive graph-bundle power has zero positive cohomology on each residue-field fiber of the original family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_residueFiber_positivePower_cohomology_subsingleton
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (x : S)
    (m : ℕ) (hm : 0 < m) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H
      ((A.graphBundle.tensorPower m).pullback (A.abelian.scheme.hom.fiberι x)).sheaf (q + 1)) := by
  let s := S.fromSpecResidueField x
  let B := A.pullback s
  let f := A.abelian.scheme.hom.fiberι x
  let e : ((A.graphBundle.tensorPower m).pullback f).sheaf ≅ (B.graphBundle.tensorPower m).sheaf :=
    Line.Bundles.LineBundle.powerBaseChangeIso f A.graphBundle m ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left m).mapIso (A.graphBundle_baseChangeIso s).symm
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap B.abelian.scheme.hom) (q + 1)
  have hz : IsZero (F.obj (B.graphBundle.tensorPower m).sheaf) :=
    B.graphBundle_positivePower_cohomology_vanishes_overField hN
      (Abelian.Schemes.level_unit_under_base_change s N hunit) m hm q
  exact ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso (F.mapIso e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
