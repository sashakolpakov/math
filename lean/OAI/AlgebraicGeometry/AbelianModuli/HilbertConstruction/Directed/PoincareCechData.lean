import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.RigidifiedFamilyLines

/-! # Poincare Cech Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareCechData.DirectedPolarizedSchemeGluing

noncomputable section

/-! The actual dual colimit cover carries a directed system of original
normalized Poincare lines. Consequently it has canonical comparisons
on all test intersections, with proved cocycle and naturality. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {S : Scheme.{0}} [IsLocallyNoetherian S] (C : S.OpenCover.{0})
  [Category C.I₀] [C.LocallyDirected] [Small.{0} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
local notation "E" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.scheme (OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualAbelian C F hN e)
local notation "DE" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualData C F hN e

abbrev poincareCover : (E).left.OpenCover.{0} := (DE).schemeData.cover

local notation "V" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareCechData.DirectedPolarizedSchemeGluing.poincareCover C F hN e

omit [IsLocallyNoetherian S] in
instance poincareCover_locallyDirected : (poincareCover C F hN e).LocallyDirected :=
  inferInstanceAs ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.dualData C F hN e).schemeData.cover.LocallyDirected)

/-- This identity on the original dual total space reconciles the
native cover structure map with the original chart structure map. -/
def poincareCoverParameterIso (i : C.I₀) :
    Embedded.FamilyOpenCover.overOpenCoverObject E V i ≅ PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameter C F i :=
  Over.isoMk (Iso.refl _) (by
    have hbase : (DE).chartMap i ≫ (DE).space.hom =
        (F i).dual.abelian.scheme.hom ≫ C.f i := (DE).chartMap_over i
    exact (Category.id_comp ((F i).dual.abelian.scheme.hom ≫ C.f i)).trans hbase.symm)

omit [IsLocallyNoetherian S] in
theorem poincareCoverParameterIso_natural {i j : C.I₀} (f : i ⟶ j) :
    Embedded.CoverComparisons.overOpenCoverTransition E V f ≫ (poincareCoverParameterIso C F hN e j).hom =
      (poincareCoverParameterIso C F hN e i).hom ≫ PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterTransition C F hN e f := by
  apply Over.OverMorphism.ext
  change (DE).transition f ≫ 𝟙 _ = 𝟙 _ ≫ (DE).transition f
  exact (Category.comp_id ((DE).transition f)).trans (Category.id_comp ((DE).transition f)).symm

omit [IsLocallyNoetherian S] in
private theorem familyClass_comp {T U W : Over S} (a : U ⟶ T) (b : T ⟶ W)
    (q : Line.Bundles.LineBundle.IsoClass (W ⊗ (A).scheme).left) :
    Line.Bundles.LineBundle.pullbackClass (a ▷ (A).scheme).left
        (Line.Bundles.LineBundle.pullbackClass (b ▷ (A).scheme).left q) =
      Line.Bundles.LineBundle.pullbackClass ((a ≫ b) ▷ (A).scheme).left q :=
  (Line.Bundles.LineBundle.pullbackClass_comp (a ▷ (A).scheme).left (b ▷ (A).scheme).left q).symm.trans
    (congrArg (fun f => Line.Bundles.LineBundle.pullbackClass f q)
      (congrArg Over.Hom.left (comp_whiskerRight a b (A).scheme).symm))

/-- Every input here is the original local Poincare object or a proved
colimit/transition equation. No line-compatibility hypothesis is added. -/
def poincareLineData : RigidifiedFamilyLines.DirectedRigidifiedFamilyLines A E V where
  line i := (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincareRigidified C F hN e i).familyPullback A
    (poincareCoverParameterIso C F hN e i).hom
  transition {i j} f := by
    let a := Embedded.CoverComparisons.overOpenCoverTransition E V f
    let bi := (poincareCoverParameterIso C F hN e i).hom
    let bj := (poincareCoverParameterIso C F hN e j).hom
    let t := PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameterTransition C F hN e f
    let Li := Line.Bundles.LineBundle.classOf (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincare C F hN e i)
    let Lj := Line.Bundles.LineBundle.classOf (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincare C F hN e j)
    have hnat : a ≫ bj = bi ≫ t := poincareCoverParameterIso_natural C F hN e f
    change Line.Bundles.LineBundle.pullbackClass (a ▷ (A).scheme).left (Line.Bundles.LineBundle.pullbackClass (bj ▷ (A).scheme).left Lj) =
      Line.Bundles.LineBundle.pullbackClass (bi ▷ (A).scheme).left Li
    exact (familyClass_comp C F hN e a bj Lj).trans
      ((congrArg (fun m : Embedded.FamilyOpenCover.overOpenCoverObject E V i ⟶ PoincareTransitions.DirectedPolarizedSchemeGluing.poincareParameter C F j =>
        Line.Bundles.LineBundle.pullbackClass (m ▷ (A).scheme).left Lj) hnat).trans
        ((familyClass_comp C F hN e bi t Lj).symm.trans
          (congrArg (Line.Bundles.LineBundle.pullbackClass (bi ▷ (A).scheme).left)
            (PoincareTransitions.DirectedPolarizedSchemeGluing.localPoincare_transition_class C F hN e f))))

/-- The original normalized lines now compare on every actual test
intersection of the dual cover, including nonreduced tests. -/
def poincareOverlapComparison {T : Over S} (i j : C.I₀)
    (a : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E V i) (b : T ⟶ Embedded.FamilyOpenCover.overOpenCoverObject E V j)
    (h : a ≫ Embedded.FamilyOpenCover.overOpenCoverMap E V i = b ≫ Embedded.FamilyOpenCover.overOpenCoverMap E V j) :
    RigidifiedLineBundles.RigidifiedLineBundleIso
      (((poincareLineData C F hN e).line i).familyPullback A a)
      (((poincareLineData C F hN e).line j).familyPullback A b) :=
  (poincareLineData C F hN e).comparison i j a b h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PoincareCechData.DirectedPolarizedSchemeGluing
