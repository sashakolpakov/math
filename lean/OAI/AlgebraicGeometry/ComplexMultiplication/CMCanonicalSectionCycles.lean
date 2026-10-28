import OAI.AlgebraicGeometry.ComplexMultiplication.HomologyFunctorCoherence
import OAI.AlgebraicGeometry.ComplexMultiplication.SectionCohomologySheafNaturality
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # CM Canonical Section Cycles -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMCanonicalSectionCycles

noncomputable section

section

/-! # When sections preserve homology, the sheafification class is the canonical comparison -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

variable (Y : TopCat.{0})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) ℤ) (n : ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sectionCohomologyPresheafToSheaf_eq_comparison
    [(sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).PreservesLeftHomologyOf
      (K.sc n)] :
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf Y K n =
      ((K.sc n).mapHomologyIso
        (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})).hom := by
  let F := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let c := asIso adj.counit
  let : PreservesFiniteLimits (G ⋙ F) := preservesFiniteLimits_of_natIso c.symm
  let : PreservesFiniteColimits (G ⋙ F) := preservesFiniteColimits_of_natIso c.symm
  let S := K.sc n
  let PK := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  let e := (PK.sc n).mapHomologyIso F
  let h := S.mapHomologyIso G
  let cc := NatIso.mapHomologicalComplex c ℤᵘᵖ
  have hc : homologyMap (cc.hom.app K) n =
      (S.mapHomologyIso (G ⋙ F)).hom ≫ c.hom.app S.homology := by
    have ht := HomologyFunctorCoherence.homologyComparison_natTrans S (G ⋙ F) (𝟭 _) c.hom
    simpa only [HomologyFunctorCoherence.homologyComparison_id, Category.comp_id, homologyMap] using! ht
  have he : (S.mapHomologyIso (G ⋙ F)).hom = e.hom ≫ F.map h.hom := by
    exact HomologyFunctorCoherence.homologyComparison_comp S G F
  unfold AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso
  change toSheafify (Opens.grothendieckTopology Y) (PK.homology n) ≫
    G.map (e.inv ≫ homologyMap (cc.hom.app K) n) = h.hom
  rw [hc, he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, G.map_comp]
  change (toSheafify (Opens.grothendieckTopology Y) (PK.homology n) ≫
    sheafifyMap (Opens.grothendieckTopology Y) h.hom) ≫ G.map (c.hom.app S.homology) = h.hom
  rw [← toSheafify_naturality, Category.assoc]
  have ht := adj.right_triangle_components S.homology
  simpa only [Category.comp_id] using! congrArg (fun g => h.hom ≫ g) ht

end

section

/-! # The canonical cohomology-sheaf class preserves the actual cocycle sections -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

variable (Y : TopCat.{0})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) ℤ) (n : ℤ)

/-- The canonical map on cocycles, expressed through the actual sheafification unit and counit. -/
def sectionCycleComparison :
    (((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).mapHomologicalComplex
      ℤᵘᵖ).obj K).cycles n ⟶
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj (K.cycles n) :=
  let F := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let P := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  let c := (NatIso.mapHomologicalComplex (asIso adj.counit) ℤᵘᵖ).hom.app K
  adj.unit.app (P.cycles n) ≫ G.map
    (((P.sc n).mapCyclesIso F).inv ≫ cyclesMap c n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sectionCycleComparison_iCycles :
    sectionCycleComparison Y K n ≫
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).map (K.iCycles n) =
    (((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).mapHomologicalComplex
      ℤᵘᵖ).obj K).iCycles n := by
  let F := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let P := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  let c := (NatIso.mapHomologicalComplex (asIso adj.counit) ℤᵘᵖ).hom.app K
  let e := (P.sc n).mapCyclesIso F
  have he : e.inv ≫ ((F.mapHomologicalComplex ℤᵘᵖ).obj P).iCycles n =
      F.map (P.iCycles n) := by
    rw [Iso.inv_comp_eq]
    exact (ShortComplex.mapCyclesIso_hom_iCycles (P.sc n) F).symm
  have hc : cyclesMap c n ≫ K.iCycles n =
      ((F.mapHomologicalComplex ℤᵘᵖ).obj P).iCycles n ≫ adj.counit.app (K.X n) := by
    simpa only [NatIso.mapHomologicalComplex] using! cyclesMap_i c n
  have hn : P.iCycles n ≫ adj.unit.app (G.obj (K.X n)) =
      adj.unit.app (P.cycles n) ≫ G.map (F.map (P.iCycles n)) := by
    exact adj.unit.naturality (P.iCycles n)
  unfold sectionCycleComparison
  change (adj.unit.app (P.cycles n) ≫ G.map (e.inv ≫ cyclesMap c n)) ≫
    G.map (K.iCycles n) = P.iCycles n
  calc
    _ = adj.unit.app (P.cycles n) ≫
        G.map (e.inv ≫ (cyclesMap c n ≫ K.iCycles n)) := by
      simp only [G.map_comp, Category.assoc]
    _ = adj.unit.app (P.cycles n) ≫
        G.map (F.map (P.iCycles n) ≫ adj.counit.app (K.X n)) := by
      rw [hc, ← Category.assoc, he]
    _ = P.iCycles n ≫ (adj.unit.app (G.obj (K.X n)) ≫
        G.map (adj.counit.app (K.X n))) := by
      rw [G.map_comp, ← Category.assoc, ← hn, Category.assoc]
    _ = P.iCycles n := by
      simpa only [Category.comp_id] using! congrArg
        (fun g => P.iCycles n ≫ g) (adj.right_triangle_components (K.X n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem sectionCohomologyPresheafToSheaf_cycles :
    (((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).mapHomologicalComplex
      ℤᵘᵖ).obj K).homologyπ n ≫
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf Y K n =
    sectionCycleComparison Y K n ≫
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}).map (K.homologyπ n) := by
  let F := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let P := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  let c := (NatIso.mapHomologicalComplex (asIso adj.counit) ℤᵘᵖ).hom.app K
  let e := (P.sc n).mapHomologyIso F
  let ec := (P.sc n).mapCyclesIso F
  have hp : ((F.mapHomologicalComplex ℤᵘᵖ).obj P).homologyπ n ≫ e.hom =
      ec.hom ≫ F.map (P.homologyπ n) := by
    exact HomologyFunctorCoherence.homologyComparison_cycles (P.sc n) F
  have he : F.map (P.homologyπ n) ≫ e.inv =
      ec.inv ≫ ((F.mapHomologicalComplex ℤᵘᵖ).obj P).homologyπ n := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hp]
    simp only [Iso.inv_hom_id_assoc]
  have hn : P.homologyπ n ≫ adj.unit.app (P.homology n) =
      adj.unit.app (P.cycles n) ≫ G.map (F.map (P.homologyπ n)) := by
    exact adj.unit.naturality (P.homologyπ n)
  have hc : ((F.mapHomologicalComplex ℤᵘᵖ).obj P).homologyπ n ≫ homologyMap c n =
      cyclesMap c n ≫ K.homologyπ n := by
    simpa only [NatIso.mapHomologicalComplex] using! homologyπ_naturality c n
  unfold AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf
    AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafSheafificationIso sectionCycleComparison
  change P.homologyπ n ≫ (adj.unit.app (P.homology n) ≫
    G.map (e.inv ≫ homologyMap c n)) =
      (adj.unit.app (P.cycles n) ≫ G.map (ec.inv ≫ cyclesMap c n)) ≫ G.map (K.homologyπ n)
  calc
    _ = adj.unit.app (P.cycles n) ≫
        G.map ((F.map (P.homologyπ n) ≫ e.inv) ≫ homologyMap c n) := by
      rw [← Category.assoc, hn]
      simp only [G.map_comp, Category.assoc]
    _ = adj.unit.app (P.cycles n) ≫
        G.map (ec.inv ≫ (cyclesMap c n ≫ K.homologyπ n)) := by
      rw [he, Category.assoc, hc]
    _ = _ := by simp only [G.map_comp, Category.assoc]

end

/-! # Canonical cocycle sections on an actual ambient open -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex

variable (Y : TopCat.{0})
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) ℤ)
  (n : ℤ) (V : Opens Y)

/-- The actual map from cocycle sections to sections of the cycle sheaf. -/
def openSectionCycleComparison :
    (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).obj K).cycles n ⟶
      (K.cycles n).obj.obj (op V) :=
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op V)
  let P := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  ((P.sc n).mapCyclesIso E).hom ≫ (sectionCycleComparison Y K n).app (op V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem openSectionCycleComparison_iCycles :
    openSectionCycleComparison Y K n V ≫ (K.iCycles n).hom.app (op V) =
      (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).obj K).iCycles n := by
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op V)
  let P := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  have hc : (sectionCycleComparison Y K n).app (op V) ≫
      (K.iCycles n).hom.app (op V) = (P.iCycles n).app (op V) := by
    simpa only [NatTrans.comp_app] using!
      congrArg (fun f => f.app (op V)) (sectionCycleComparison_iCycles Y K n)
  unfold openSectionCycleComparison
  rw [Category.assoc, hc]
  exact ShortComplex.mapCyclesIso_hom_iCycles (P.sc n) E

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem openSectionCohomology_cycles :
    (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).obj K).homologyπ n ≫
      AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection Y K n V =
    openSectionCycleComparison Y K n V ≫ (K.homologyπ n).hom.app (op V) := by
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op V)
  let P := (G.mapHomologicalComplex ℤᵘᵖ).obj K
  have hp : (((AlgebraicTopology.Support.DerivedSectionsLocalization.TopCat.Sheaf.supportEvaluation Y V).mapHomologicalComplex ℤᵘᵖ).obj K).homologyπ n ≫
      (AlgebraicTopology.Sheaf.CohomologyStalkVanishing.TopCat.sectionCohomologyPresheafOnOpenIso Y K n V).hom =
      ((P.sc n).mapCyclesIso E).hom ≫ (P.homologyπ n).app (op V) := by
    exact HomologyFunctorCoherence.homologyComparison_cycles (P.sc n) E
  have hc : (P.homologyπ n).app (op V) ≫
      (AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyPresheafToSheaf Y K n).app (op V) =
      (sectionCycleComparison Y K n).app (op V) ≫ (K.homologyπ n).hom.app (op V) := by
    simpa only [NatTrans.comp_app] using!
      congrArg (fun f => f.app (op V)) (sectionCohomologyPresheafToSheaf_cycles Y K n)
  unfold AlgebraicTopology.Sheaf.CohomologySection.TopCat.sectionCohomologyToSheafSection openSectionCycleComparison
  rw [← Category.assoc, hp, Category.assoc, hc, ← Category.assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMCanonicalSectionCycles
