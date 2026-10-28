import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.StructureCohomologyBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FaithfulFlatCohomologyVanishing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Structure Cohomology Field Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The sharp structure-sheaf cohomology bound descends from an algebraic closure to every field, including finite fields, through the actual faithfully flat cohomology comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.structure_cohomology_vanish_above_dimension
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (q : ℕ) (hq : g < q) :
    IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) q).obj (Line.Bundles.structureModule A.abelian.scheme.left)) := by
  have : A.abelian.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.abelian.scheme.hom]
    infer_instance⟩
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  let φ : CommRingCat.of K ⟶ CommRingCat.of (AlgebraicClosure K) :=
    CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))
  let f := Spec.map φ
  let B := A.pullback f
  let a := pullback.fst A.abelian.scheme.hom f
  let b := pullback.snd A.abelian.scheme.hom f
  have H : IsPullback a b A.abelian.scheme.hom f :=
    IsPullback.of_hasPullback A.abelian.scheme.hom f
  have hNF : (N : AlgebraicClosure K) ≠ 0 := by
    intro hz
    apply hNk
    apply (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_natCast, map_zero] using hz
  have hB := B.structure_cohomology_vanish_above_dimension_of_infinite hN hNF q hq
  let L := Line.Bundles.LineBundle.trivial A.abelian.scheme.left
  have hPB : IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap B.abelian.scheme.hom) q).obj (L.pullback a).sheaf) :=
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap B.abelian.scheme.hom) q).mapIso
        (Line.Bundles.structureModulePullbackIso a)).isZero_iff.mpr hB
  have hsource : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q) :=
    ModuleCat.subsingleton_of_isZero hPB
  have htarget : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H L.sheaf q) :=
    (FaithfulFlatCohomologyVanishing.fieldExtensionLineBundle_cohomology_vanish_iff H L q).mp hsource
  have : Subsingleton ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap A.abelian.scheme.hom) q).obj (Line.Bundles.structureModule A.abelian.scheme.left)) := htarget
  exact ModuleCat.isZero_of_subsingleton _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
