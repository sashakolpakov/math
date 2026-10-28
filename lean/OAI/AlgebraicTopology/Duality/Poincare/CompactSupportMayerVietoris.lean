import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportPairDiagram
import OAI.AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris
import OAI.AlgebraicTopology.Duality.Poincare.CohomologyMayerVietorisNaturality
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! # Compact Support Mayer Vietoris -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportMayerVietoris

noncomputable section

/-!
# Mayer--Vietoris for actual compactly supported rational cohomology

Closed-support Mayer--Vietoris is taken through the filtered system of
actual compact pairs. Cofinality identifies the four resulting colimits
with compact supports inside the opens; proved excision then identifies
these with the native compact-support cohomology of the open subspaces.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exact_of_evaluations {J : Type} [SmallCategory J]
    (S : ShortComplex (J ⥤ ModuleCat.{0} ℚ))
    (hS : ∀ j, (S.map ((evaluation J (ModuleCat.{0} ℚ)).obj j)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, Functor.isZero_iff]
  intro j
  exact ((S.map ((evaluation J (ModuleCat.{0} ℚ)).obj j)).exact_iff_isZero_homology.mp
    (hS j)).of_iso (S.mapHomologyIso ((evaluation J (ModuleCat.{0} ℚ)).obj j)).symm

variable {X : TopCat.{0}} [T2Space X]

/-- The first two Mayer--Vietoris maps form an actual short complex of compact-pair diagrams. -/
def compactSupportPairFirstSecondSequence (U V : Opens X) (n : ℕ) :
    ShortComplex ((U.compactsInside × V.compactsInside) ⥤ ModuleCat.{0} ℚ) :=
  ShortComplex.mk (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportPairSecond (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportPairFirst_second (ModuleCat.of ℚ ℚ) U V n)

/-- Exactness on compact pairs comes from the proved closed-support sequence. -/
theorem compactSupportPairFirstSecondSequence_exact (U V : Opens X) (n : ℕ) :
    (compactSupportPairFirstSecondSequence U V n).Exact := by
  apply exact_of_evaluations
  intro p
  exact (SupportCohomologyMayerVietoris.compactSupportStageMayerVietorisSequence_exact X p.1.val p.2.val n).exact 0

/-- The actual first two maps between ambient compact-support colimits. -/
def compactSupportInsideMayerVietorisFirstSecondSequence (U V : Opens X) (n : ℕ) :
    ShortComplex (ModuleCat.{0} ℚ) :=
  ShortComplex.mk (CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportInsideMayerVietorisSecond (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst_second (ModuleCat.of ℚ ℚ) U V n)

/-- Filtered exactness and actual cofinality give exactness at the two-open direct sum. -/
theorem compactSupportInsideMayerVietorisFirstSecondSequence_exact (U V : Opens X) (n : ℕ) :
    (compactSupportInsideMayerVietorisFirstSecondSequence U V n).Exact := by
  let : IsFiltered U.compactsInside := CompactSupportPairIndex.compactSupportsInside_isFiltered U
  let : IsFiltered V.compactsInside := CompactSupportPairIndex.compactSupportsInside_isFiltered V
  apply ShortComplex.exact_of_iso (S₁ := (compactSupportPairFirstSecondSequence U V n).map colim)
    (S₂ := compactSupportInsideMayerVietorisFirstSecondSequence U V n)
    (ShortComplex.isoMk
      (CompactSupportPairIndex.compactSupportPairIntersectionColimitIso (ModuleCat.of ℚ ℚ) U V n)
      (CompactSupportPairDiagram.compactSupportPairMiddleColimitIso (ModuleCat.of ℚ ℚ) U V n)
      (CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V n)
      (CompactSupportPairDiagram.compactSupportPairFirst_colimit (ModuleCat.of ℚ ℚ) U V n).symm
      (CompactSupportPairDiagram.compactSupportPairSecond_colimit (ModuleCat.of ℚ ℚ) U V n).symm)
  exact (compactSupportPairFirstSecondSequence_exact U V n).map colim

/-- Actual open extension from the intersection to the two opens, with signs `(+, +)`. -/
def compactSupportMayerVietorisFirst (U V : Opens X) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊓ V)) n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⊞
        CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) n :=
  biprod.lift (CompactSupportOpen.compactSupportOpenMap (show U ⊓ V ≤ U from inf_le_left) n)
    (CompactSupportOpen.compactSupportOpenMap (show U ⊓ V ≤ V from inf_le_right) n)

/-- The difference of the actual open extensions into the union. -/
def compactSupportMayerVietorisSecond (U V : Opens X) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) n ⊞
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V) n ⟶
        CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊔ V)) n :=
  biprod.desc (CompactSupportOpen.compactSupportOpenMap (show U ≤ U ⊔ V from le_sup_left) n)
    (-CompactSupportOpen.compactSupportOpenMap (show V ≤ U ⊔ V from le_sup_right) n)

@[reassoc (attr := simp)]
theorem compactSupportMayerVietorisFirst_second (U V : Opens X) (n : ℕ) :
    compactSupportMayerVietorisFirst U V n ≫ compactSupportMayerVietorisSecond U V n = 0 := by
  simp only [compactSupportMayerVietorisFirst, compactSupportMayerVietorisSecond,
    biprod.lift_desc, Preadditive.comp_neg, CompactSupportOpen.compactSupportOpenMap_comp, add_neg_cancel]

/-- The native first map agrees with the compact-support index comparison. -/
@[reassoc]
theorem compactSupportMayerVietorisFirst_index (U V : Opens X) (n : ℕ) :
    CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V n ≫
        (biprod.mapIso (CompactSupportOpen.compactSupportOpenIndexIso U n) (CompactSupportOpen.compactSupportOpenIndexIso V n)).hom =
      (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) n).hom ≫ compactSupportMayerVietorisFirst U V n := by
  apply biprod.hom_ext <;>
    simp [CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst, compactSupportMayerVietorisFirst]

/-- The native difference map agrees with the compact-support index comparison. -/
@[reassoc]
theorem compactSupportMayerVietorisSecond_index (U V : Opens X) (n : ℕ) :
    CompactSupportPairDiagram.compactSupportInsideMayerVietorisSecond (ModuleCat.of ℚ ℚ) U V n ≫
        (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n).hom =
      (biprod.mapIso (CompactSupportOpen.compactSupportOpenIndexIso U n) (CompactSupportOpen.compactSupportOpenIndexIso V n)).hom ≫
        compactSupportMayerVietorisSecond U V n := by
  apply biprod.hom_ext' <;>
    simp [CompactSupportPairDiagram.compactSupportInsideMayerVietorisSecond, compactSupportMayerVietorisSecond]

/-- The actual first two maps of compact-support Mayer--Vietoris. -/
def compactSupportMayerVietorisFirstSecondSequence (U V : Opens X) (n : ℕ) :
    ShortComplex (ModuleCat.{0} ℚ) :=
  ShortComplex.mk (compactSupportMayerVietorisFirst U V n)
    (compactSupportMayerVietorisSecond U V n) (compactSupportMayerVietorisFirst_second U V n)

/-- Exactness at `Hc(U) ⊕ Hc(V)`, with the actual extension maps. -/
theorem compactSupportMayerVietorisFirstSecondSequence_exact (U V : Opens X) (n : ℕ) :
    (compactSupportMayerVietorisFirstSecondSequence U V n).Exact :=
  ShortComplex.exact_of_iso (ShortComplex.isoMk
    (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) n)
    (biprod.mapIso (CompactSupportOpen.compactSupportOpenIndexIso U n) (CompactSupportOpen.compactSupportOpenIndexIso V n))
    (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n)
    (compactSupportMayerVietorisFirst_index U V n).symm
    (compactSupportMayerVietorisSecond_index U V n).symm)
    (compactSupportInsideMayerVietorisFirstSecondSequence_exact U V n)

/-- The genuine closed-support connecting maps form a natural transformation
on actual compact pairs. -/
def compactSupportPairBoundary (U V : Opens X) (n : ℕ) :
    CompactSupportPairIndex.compactSupportPairUnionDiagram (ModuleCat.of ℚ ℚ) U V n ⟶
      CompactSupportPairIndex.compactSupportPairIntersectionDiagram (ModuleCat.of ℚ ℚ) U V (n + 1) where
  app p := SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X p.1.val p.2.val
    p.1.val.isCompact.isClosed p.2.val.isCompact.isClosed n
  naturality p q f :=
    CohomologyMayerVietorisNaturality.supportCohomologyMayerVietorisBoundary_naturality X
      (show (p.1.val : Set X) ⊆ q.1.val from leOfHom f.1)
      (show (p.2.val : Set X) ⊆ q.2.val from leOfHom f.2)
      p.1.val.isCompact.isClosed p.2.val.isCompact.isClosed
      q.1.val.isCompact.isClosed q.2.val.isCompact.isClosed n

/-- Six consecutive terms of the actual compact-pair diagram. -/
def compactSupportPairMayerVietorisSequence (U V : Opens X) (n : ℕ) :
    ComposableArrows ((U.compactsInside × V.compactsInside) ⥤ ModuleCat.{0} ℚ) 5 :=
  ComposableArrows.mk₅ (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportPairSecond (ModuleCat.of ℚ ℚ) U V n) (compactSupportPairBoundary U V n)
    (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V (n + 1))
    (CompactSupportPairDiagram.compactSupportPairSecond (ModuleCat.of ℚ ℚ) U V (n + 1))

/-- Evaluation is precisely the previously proved sequence at that compact pair. -/
def compactSupportPairMayerVietorisEvaluationIso (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    ((((evaluation (U.compactsInside × V.compactsInside) (ModuleCat.{0} ℚ)).obj p).mapComposableArrows 5).obj
      (compactSupportPairMayerVietorisSequence U V n)) ≅
      SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisSequence X p.1.val p.2.val
        p.1.val.isCompact.isClosed p.2.val.isCompact.isClosed n := by
  refine ComposableArrows.isoMk₅ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ ?_
  all_goals simp
  all_goals rfl

/-- Pointwise support exactness proves exactness of the whole compact-pair diagram. -/
theorem compactSupportPairMayerVietorisSequence_exact (U V : Opens X) (n : ℕ) :
    (compactSupportPairMayerVietorisSequence U V n).Exact := by
  have hpoint (p : U.compactsInside × V.compactsInside) :
      (((((evaluation (U.compactsInside × V.compactsInside) (ModuleCat.{0} ℚ)).obj p).mapComposableArrows 5).obj
      (compactSupportPairMayerVietorisSequence U V n))).Exact :=
    ComposableArrows.exact_of_iso (compactSupportPairMayerVietorisEvaluationIso U V n p).symm
      (SupportCohomologyMayerVietoris.compactSupportStageMayerVietorisSequence_exact X p.1.val p.2.val n)
  refine { zero := ?_, exact := ?_ }
  · intro i hi
    apply NatTrans.ext
    funext p
    exact (hpoint p).zero i hi
  · intro i hi
    apply exact_of_evaluations
    intro p
    exact (hpoint p).exact i hi

/-- The connecting map on the actual ambient compact-support colimits. -/
def compactSupportInsideMayerVietorisBoundary (U V : Opens X) (n : ℕ) :
    CompactSupportInsideMaps.compactSupportedInsideCohomology (ModuleCat.of ℚ ℚ) (U ⊔ V) n ⟶
      CompactSupportInsideMaps.compactSupportedInsideCohomology (ModuleCat.of ℚ ℚ) (U ⊓ V) (n + 1) :=
  (CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V n).inv ≫
    colimMap (compactSupportPairBoundary U V n) ≫
    (CompactSupportPairIndex.compactSupportPairIntersectionColimitIso (ModuleCat.of ℚ ℚ) U V (n + 1)).hom

/-- On any genuine compact pair, the colimit connecting map is the actual
closed-support connecting map followed by its compact-stage insertion. -/
@[reassoc (attr := simp)]
theorem compactSupportInsideMayerVietorisBoundary_stage (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) (U ⊔ V) n)
        (CompactSupportDecomposition.compactPairUnion U V p) ≫ compactSupportInsideMayerVietorisBoundary U V n =
      SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X p.1.val p.2.val
        p.1.val.isCompact.isClosed p.2.val.isCompact.isClosed n ≫
      colimit.ι (CompactSupportInsideMaps.compactSupportInsideDiagram (ModuleCat.of ℚ ℚ) (U ⊓ V) (n + 1))
        (CompactSupportPairIndex.compactPairIntersection U V p) := by
  rw [← CompactSupportPairIndex.compactSupportPairUnionColimitIso_ι (ModuleCat.of ℚ ℚ) U V n p]
  simp only [compactSupportInsideMayerVietorisBoundary, Category.assoc, Iso.hom_inv_id_assoc,
    ι_colimMap_assoc, CompactSupportPairIndex.compactSupportPairIntersectionColimitIso_ι, compactSupportPairBoundary]

/-- The six-term Mayer--Vietoris sequence in ambient compact-support colimits. -/
def compactSupportInsideMayerVietorisSequence (U V : Opens X) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℚ) 5 :=
  ComposableArrows.mk₅ (CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportInsideMayerVietorisSecond (ModuleCat.of ℚ ℚ) U V n)
    (compactSupportInsideMayerVietorisBoundary U V n)
    (CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V (n + 1))
    (CompactSupportPairDiagram.compactSupportInsideMayerVietorisSecond (ModuleCat.of ℚ ℚ) U V (n + 1))

/-- The colimit of the compact-pair sequence is canonically the ambient
compact-support sequence, including its connecting map. -/
def compactSupportInsideMayerVietorisSequenceIso (U V : Opens X) (n : ℕ) :
    (((colim : ((U.compactsInside × V.compactsInside) ⥤ ModuleCat.{0} ℚ) ⥤
      ModuleCat.{0} ℚ).mapComposableArrows 5).obj
        (compactSupportPairMayerVietorisSequence U V n)) ≅
      compactSupportInsideMayerVietorisSequence U V n := by
  refine ComposableArrows.isoMk₅
    (CompactSupportPairIndex.compactSupportPairIntersectionColimitIso (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairDiagram.compactSupportPairMiddleColimitIso (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V n)
    (CompactSupportPairIndex.compactSupportPairIntersectionColimitIso (ModuleCat.of ℚ ℚ) U V (n + 1))
    (CompactSupportPairDiagram.compactSupportPairMiddleColimitIso (ModuleCat.of ℚ ℚ) U V (n + 1))
    (CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V (n + 1)) ?_ ?_ ?_ ?_ ?_
  · exact CompactSupportPairDiagram.compactSupportPairFirst_colimit (ModuleCat.of ℚ ℚ) U V n
  · exact CompactSupportPairDiagram.compactSupportPairSecond_colimit (ModuleCat.of ℚ ℚ) U V n
  · change colimMap (compactSupportPairBoundary U V n) ≫ _ =
      (CompactSupportPairIndex.compactSupportPairUnionColimitIso (ModuleCat.of ℚ ℚ) U V n).hom ≫
        compactSupportInsideMayerVietorisBoundary U V n
    rw [compactSupportInsideMayerVietorisBoundary, Iso.hom_inv_id_assoc]
  · exact CompactSupportPairDiagram.compactSupportPairFirst_colimit (ModuleCat.of ℚ ℚ) U V (n + 1)
  · exact CompactSupportPairDiagram.compactSupportPairSecond_colimit (ModuleCat.of ℚ ℚ) U V (n + 1)

/-- Exactness survives the actual filtered compact-support colimit. -/
theorem compactSupportInsideMayerVietorisSequence_exact (U V : Opens X) (n : ℕ) :
    (compactSupportInsideMayerVietorisSequence U V n).Exact := by
  let : IsFiltered U.compactsInside := CompactSupportPairIndex.compactSupportsInside_isFiltered U
  let : IsFiltered V.compactsInside := CompactSupportPairIndex.compactSupportsInside_isFiltered V
  apply ComposableArrows.exact_of_iso (compactSupportInsideMayerVietorisSequenceIso U V n)
  have hS := compactSupportPairMayerVietorisSequence_exact U V n
  refine { zero := ?_, exact := ?_ }
  · intro i hi
    change colim.map _ ≫ colim.map _ = 0
    rw [← Functor.map_comp, hS.zero i hi, Functor.map_zero]
  · intro i hi
    exact (hS.exact i hi).map colim

/-- The actual connecting map in compactly supported rational cohomology. -/
def compactSupportMayerVietorisBoundary (U V : Opens X) (n : ℕ) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊔ V)) n ⟶
      CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of ↥(U ⊓ V)) (n + 1) :=
  (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n).inv ≫
    compactSupportInsideMayerVietorisBoundary U V n ≫
    (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) (n + 1)).hom

/-- The native connecting map is exactly the compact-support colimit connecting map. -/
@[reassoc (attr := simp)]
theorem compactSupportMayerVietorisBoundary_index (U V : Opens X) (n : ℕ) :
    (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n).hom ≫ compactSupportMayerVietorisBoundary U V n =
      compactSupportInsideMayerVietorisBoundary U V n ≫
        (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) (n + 1)).hom := by
  simp only [compactSupportMayerVietorisBoundary, Iso.hom_inv_id_assoc]

/-- The native connecting map has the same actual closed-support representative. -/
@[reassoc (attr := simp)]
theorem compactSupportMayerVietorisBoundary_stage (U V : Opens X) (n : ℕ)
    (p : U.compactsInside × V.compactsInside) :
    CompactSupportOpen.compactSupportOpenStageClass (U ⊔ V) (CompactSupportDecomposition.compactPairUnion U V p) n ≫
        compactSupportMayerVietorisBoundary U V n =
      SupportCohomologyMayerVietoris.supportCohomologyMayerVietorisBoundary X p.1.val p.2.val
        p.1.val.isCompact.isClosed p.2.val.isCompact.isClosed n ≫
      CompactSupportOpen.compactSupportOpenStageClass (U ⊓ V) (CompactSupportPairIndex.compactPairIntersection U V p) (n + 1) := by
  simp only [CompactSupportOpen.compactSupportOpenStageClass, Category.assoc,
    compactSupportMayerVietorisBoundary_index,
    compactSupportInsideMayerVietorisBoundary_stage_assoc]

/-- Six consecutive terms of compact-support Mayer--Vietoris, with actual
open extensions and the actual closed-support connecting map. -/
def compactSupportMayerVietorisSequence (U V : Opens X) (n : ℕ) :
    ComposableArrows (ModuleCat.{0} ℚ) 5 :=
  ComposableArrows.mk₅ (compactSupportMayerVietorisFirst U V n)
    (compactSupportMayerVietorisSecond U V n) (compactSupportMayerVietorisBoundary U V n)
    (compactSupportMayerVietorisFirst U V (n + 1))
    (compactSupportMayerVietorisSecond U V (n + 1))

/-- Every native term and arrow agrees with the proved ambient support sequence. -/
def compactSupportMayerVietorisSequenceIso (U V : Opens X) (n : ℕ) :
    compactSupportInsideMayerVietorisSequence U V n ≅ compactSupportMayerVietorisSequence U V n := by
  refine ComposableArrows.isoMk₅ (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) n)
    (biprod.mapIso (CompactSupportOpen.compactSupportOpenIndexIso U n) (CompactSupportOpen.compactSupportOpenIndexIso V n))
    (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) n) (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) (n + 1))
    (biprod.mapIso (CompactSupportOpen.compactSupportOpenIndexIso U (n + 1))
      (CompactSupportOpen.compactSupportOpenIndexIso V (n + 1)))
    (CompactSupportOpen.compactSupportOpenIndexIso (U ⊔ V) (n + 1)) ?_ ?_ ?_ ?_ ?_
  · exact compactSupportMayerVietorisFirst_index U V n
  · exact compactSupportMayerVietorisSecond_index U V n
  · exact (compactSupportMayerVietorisBoundary_index U V n).symm
  · exact compactSupportMayerVietorisFirst_index U V (n + 1)
  · exact compactSupportMayerVietorisSecond_index U V (n + 1)

/-- Mayer--Vietoris exactness for the actual compactly supported rational
cohomology of two opens in any Hausdorff space. -/
theorem compactSupportMayerVietorisSequence_exact (U V : Opens X) (n : ℕ) :
    (compactSupportMayerVietorisSequence U V n).Exact :=
  ComposableArrows.exact_of_iso (compactSupportMayerVietorisSequenceIso U V n)
    (compactSupportInsideMayerVietorisSequence_exact U V n)

theorem compactSupportMayerVietoris_range_first (U V : Opens X) (n : ℕ) :
    LinearMap.range (compactSupportMayerVietorisFirst U V n).hom =
      LinearMap.ker (compactSupportMayerVietorisSecond U V n).hom :=
  ((compactSupportMayerVietorisSequence_exact U V n).exact 0).moduleCat_range_eq_ker

theorem compactSupportMayerVietoris_range_second (U V : Opens X) (n : ℕ) :
    LinearMap.range (compactSupportMayerVietorisSecond U V n).hom =
      LinearMap.ker (compactSupportMayerVietorisBoundary U V n).hom :=
  ((compactSupportMayerVietorisSequence_exact U V n).exact 1).moduleCat_range_eq_ker

theorem compactSupportMayerVietoris_range_boundary (U V : Opens X) (n : ℕ) :
    LinearMap.range (compactSupportMayerVietorisBoundary U V n).hom =
      LinearMap.ker (compactSupportMayerVietorisFirst U V (n + 1)).hom :=
  ((compactSupportMayerVietorisSequence_exact U V n).exact 2).moduleCat_range_eq_ker

/-- Vanishing of the next intersection group makes the difference of open
extensions surjective; no dimension-vanishing theorem is assumed globally. -/
theorem compactSupportMayerVietorisSecond_epi_of_isZero (U V : Opens X) (n : ℕ)
    (h : IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ↥(U ⊓ V)) (n + 1))) : Epi (compactSupportMayerVietorisSecond U V n) :=
  ((compactSupportMayerVietorisSequence_exact U V n).exact 1).epi_f (h.eq_of_tgt _ _)

/-- The pair diagram starts injectively in degree zero. -/
theorem compactSupportPairFirst_zero_mono (U V : Opens X) :
    Mono (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V 0) := by
  let : ∀ p : U.compactsInside × V.compactsInside,
      Mono ((CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V 0).app p) := fun p =>
    CohomologyMayerVietorisNaturality.supportCohomologyMayerVietorisFirst_zero_mono X p.1.val p.2.val
      p.1.val.isCompact.isClosed p.2.val.isCompact.isClosed
  exact NatTrans.mono_of_mono_app _

/-- The ambient compact-support sequence starts injectively in degree zero. -/
theorem compactSupportInsideMayerVietorisFirst_zero_mono (U V : Opens X) :
    Mono (CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V 0) := by
  let : IsFiltered U.compactsInside := CompactSupportPairIndex.compactSupportsInside_isFiltered U
  let : IsFiltered V.compactsInside := CompactSupportPairIndex.compactSupportsInside_isFiltered V
  let : Mono (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V 0) :=
    compactSupportPairFirst_zero_mono U V
  let : Mono (colimMap (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V 0)) := by
    change Mono ((colim : ((U.compactsInside × V.compactsInside) ⥤ ModuleCat.{0} ℚ) ⥤
      ModuleCat.{0} ℚ).map (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V 0))
    infer_instance
  have he : CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V 0 =
      (CompactSupportPairIndex.compactSupportPairIntersectionColimitIso (ModuleCat.of ℚ ℚ) U V 0).inv ≫
        colimMap (CompactSupportPairDiagram.compactSupportPairFirst (ModuleCat.of ℚ ℚ) U V 0) ≫
        (CompactSupportPairDiagram.compactSupportPairMiddleColimitIso (ModuleCat.of ℚ ℚ) U V 0).hom := by
    rw [CompactSupportPairDiagram.compactSupportPairFirst_colimit, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- The native compact-support Mayer--Vietoris sequence starts injectively. -/
theorem compactSupportMayerVietorisFirst_zero_mono (U V : Opens X) :
    Mono (compactSupportMayerVietorisFirst U V 0) := by
  let : Mono (CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V 0) :=
    compactSupportInsideMayerVietorisFirst_zero_mono U V
  have he : compactSupportMayerVietorisFirst U V 0 =
      (CompactSupportOpen.compactSupportOpenIndexIso (U ⊓ V) 0).inv ≫
        CompactSupportPairDiagram.compactSupportInsideMayerVietorisFirst (ModuleCat.of ℚ ℚ) U V 0 ≫
        (biprod.mapIso (CompactSupportOpen.compactSupportOpenIndexIso U 0) (CompactSupportOpen.compactSupportOpenIndexIso V 0)).hom := by
    rw [compactSupportMayerVietorisFirst_index, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportMayerVietoris
