import OAI.AlgebraicGeometry.ComplexMultiplication.CMCanonicalSectionCycles
import OAI.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology

/-! # Open Restricted Section Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenRestrictedSectionNormalization

noncomputable section

/-! # The original open-restricted lowest-degree comparison is the canonical class map -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

variable (Y : TopCat.{0}) (U : Opens Y)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem openRestrictedLowestSectionCohomologyIso_normalization (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{0}).mapHomologicalComplex
        ℤᵘᵖ).obj K).homology j))
    (hflasque : ∀ j, TopCat.Sheaf.IsFlasque (K.X j)) :
    (AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictedLowestSectionCohomologyIso Y U K N n hK hflasque).hom =
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection Y K n U := by
  let R : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0} ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{0} :=
    U.isOpenEmbedding.sheafPullback AddCommGrpCat.{0}
  let : R.Additive := AlgebraicTopology.Sheaf.OpenRestriction.TopCat.openSheafRestriction_additive Y U
  let : PreservesFiniteLimits R := AlgebraicTopology.Sheaf.OpenRestriction.TopCat.openSheafRestriction_preservesFiniteLimits Y U
  let : PreservesFiniteColimits R := AlgebraicTopology.Sheaf.OpenRestriction.TopCat.openSheafRestriction_preservesFiniteColimits Y U
  let A : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0} :=
    AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y U
  let B : Sheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{0} ⥤
      AddCommGrpCat.{0} := AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation (TopCat.of U) ⊤
  let : A.Additive := { map_add := by intros; rfl }
  let : B.Additive := { map_add := by intros; rfl }
  let : PreservesFiniteLimits A := comp_preservesFiniteLimits
    (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U))
  let L := (R.mapHomologicalComplex ℤᵘᵖ).obj K
  let AK := (A.mapHomologicalComplex ℤᵘᵖ).obj K
  let BL := (B.mapHomologicalComplex ℤᵘᵖ).obj L
  let q : R ⋙ B ≅ A := AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictionTopSectionsIso Y U
  let e : BL ≅ AK := AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictionTopSectionComplexIso Y U K
  let cr := (K.sc n).mapCyclesIso R
  let hr := (K.sc n).mapHomologyIso R
  let a := cyclesMap e.inv n ≫ CMCanonicalSectionCycles.openSectionCycleComparison (TopCat.of U) L n ⊤ ≫
    B.map cr.hom ≫ (q.app (K.cycles n)).hom
  have hqi : B.map (R.map (K.iCycles n)) ≫ (q.app (K.X n)).hom =
      (q.app (K.cycles n)).hom ≫ A.map (K.iCycles n) := by
    exact q.hom.naturality (K.iCycles n)
  have hri : cr.hom ≫ R.map (K.iCycles n) = L.iCycles n := by
    exact ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) R
  have hgi : CMCanonicalSectionCycles.openSectionCycleComparison (TopCat.of U) L n ⊤ ≫
      B.map (L.iCycles n) = BL.iCycles n := by
    exact CMCanonicalSectionCycles.openSectionCycleComparison_iCycles (TopCat.of U) L n ⊤
  have hei : cyclesMap e.inv n ≫ BL.iCycles n = AK.iCycles n ≫ e.inv.f n := by
    exact cyclesMap_i e.inv n
  have heq : e.inv.f n ≫ (q.app (K.X n)).hom = 𝟙 (AK.X n) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using!
      congrArg (fun f => f.f n) e.inv_hom_id
  have hai : a ≫ A.map (K.iCycles n) = AK.iCycles n := by
    have hg : (cyclesMap e.inv n ≫ CMCanonicalSectionCycles.openSectionCycleComparison (TopCat.of U) L n ⊤) ≫
        B.map (L.iCycles n) ≫ (q.app (K.X n)).hom =
        (cyclesMap e.inv n ≫ BL.iCycles n) ≫ (q.app (K.X n)).hom := by
      simpa only [Category.assoc] using! congrArg
        (fun f => cyclesMap e.inv n ≫ f ≫ (q.app (K.X n)).hom) hgi
    dsimp only [a]
    rw [Category.assoc, Category.assoc, Category.assoc, ← hqi,
      ← B.map_comp_assoc, hri,
      ← Category.assoc, ← Category.assoc]
    change (cyclesMap e.inv n ≫ CMCanonicalSectionCycles.openSectionCycleComparison (TopCat.of U) L n ⊤) ≫
      B.map (L.iCycles n) ≫ (q.app (K.X n)).hom = _
    rw [hg, hei, Category.assoc, heq]
    exact Category.comp_id _
  have ha : a = CMCanonicalSectionCycles.openSectionCycleComparison Y K n U := by
    apply (cancel_mono (A.map (K.iCycles n))).mp
    exact hai.trans (CMCanonicalSectionCycles.openSectionCycleComparison_iCycles Y K n U).symm
  have hep : AK.homologyπ n ≫ homologyMap e.inv n =
      cyclesMap e.inv n ≫ BL.homologyπ n := by
    exact homologyπ_naturality e.inv n
  have hgp : BL.homologyπ n ≫
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of U) L n ⊤ =
      CMCanonicalSectionCycles.openSectionCycleComparison (TopCat.of U) L n ⊤ ≫ B.map (L.homologyπ n) := by
    exact CMCanonicalSectionCycles.openSectionCohomology_cycles (TopCat.of U) L n ⊤
  have hrp : L.homologyπ n ≫ hr.hom = cr.hom ≫ R.map (K.homologyπ n) := by
    exact HomologyFunctorCoherence.homologyComparison_cycles (K.sc n) R
  have hqp : B.map (R.map (K.homologyπ n)) ≫ (q.app (K.homology n)).hom =
      (q.app (K.cycles n)).hom ≫ A.map (K.homologyπ n) := by
    exact q.hom.naturality (K.homologyπ n)
  apply (cancel_epi (AK.homologyπ n)).mp
  have hb : (AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology.TopCat.openRestrictedLowestSectionCohomologyIso Y U K N n hK hflasque).hom =
      homologyMap e.inv n ≫
        AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection (TopCat.of U) L n ⊤ ≫
          B.map hr.hom ≫ (q.app (K.homology n)).hom := by
    rfl
  rw [hb, ← Category.assoc, ← Category.assoc, ← Category.assoc, hep]
  simp only [Category.assoc]
  rw [← Category.assoc (BL.homologyπ n), hgp, Category.assoc,
    ← B.map_comp_assoc, hrp, B.map_comp,
    Category.assoc, hqp]
  change a ≫ A.map (K.homologyπ n) = _
  rw [ha]
  exact (CMCanonicalSectionCycles.openSectionCohomology_cycles Y K n U).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenRestrictedSectionNormalization
