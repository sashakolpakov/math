import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.FiberwiseVanishing

/-! # Cartesian Vanishing Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CartesianVanishingReflection

noncomputable section

/-! Genuine cohomology vanishing is independent of the chosen Cartesian
model of a field fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem lineBundle_fieldCartesian_cohomology_vanish_iff
    {X S Y : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ S) [IsProper f] (L : Line.Bundles.LineBundle X)
    (s : Spec (.of K) ⟶ S) {a : Y ⟶ X} {b : Y ⟶ Spec (.of K)}
    (H : IsPullback a b f s) (q : ℕ) :
    Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback (pullback.fst f s)).sheaf q) ↔
      Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (L.pullback a).sheaf q) := by
  refine ⟨ProperFlat.FiberwiseVanishing.lineBundle_fieldCartesian_cohomology_vanish f L s H q, ?_⟩
  intro hzero
  let e := H.isoPullback
  let N := L.pullback (pullback.fst f s)
  have : (pullback f s).IsSeparated := by
    constructor
    rw [← terminal.comp_from (pullback.snd f s)]
    infer_instance
  let eN : (N.pullback e.hom).sheaf ≅ (L.pullback a).sheaf :=
    (Scheme.Modules.pullbackComp e.hom (pullback.fst f s)).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr H.isoPullback_hom_fst).app L.sheaf
  let d := (Zariski.Cohomology.ZariskiCohomology.zariskiFunctor Y q).mapIso eN
  have hc : Subsingleton (Zariski.Cohomology.ZariskiCohomology.H (N.pullback e.hom).sheaf q) :=
    ⟨fun x y => (AddCommGrpCat.mono_iff_injective d.hom).mp inferInstance
      (hzero.elim _ _)⟩
  let c := CohomologyPullbackIso.lineBundleCohomologyPullbackIso e.hom (pullback.snd f s) N q
  exact ⟨fun x y => (ModuleCat.mono_iff_injective c.inv).mp inferInstance
    (hc.elim _ _)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CartesianVanishingReflection
