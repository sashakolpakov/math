import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.PolarizedSchemeGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.OpenDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSectionExt

/-! # Level Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.LevelGluing.DirectedPolarizedSchemeGluing

noncomputable section

/-! The ordered level on the effectively glued abelian scheme is recovered
from the original chart levels. Compatibility is proved from the labelled
sections and the actual Cartesian chart maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem transported_section_projection {C : Type*} [Category* C]
    {V X Y Z : C} (s : V ⟶ X) (t : V ⟶ Y) (e : X ⟶ Y) (p : Y ⟶ Z) (q : X ⟶ Z)
    (ht : t = s ≫ e) (he : e ≫ p = q) : t ≫ p = s ≫ q := by
  rw [ht, Category.assoc, he]

private theorem section_total_projection {C : Type*} [Category* C]
    {V X Y Z : C} (s : V ⟶ X) (e : X ⟶ Y) (p : Y ⟶ Z) (t : V ⟶ Y) (r : V ⟶ Z)
    (hs : s ≫ e = t) (hp : t ≫ p = r) : s ≫ (e ≫ p) = r := by
  rw [← Category.assoc, hs, hp]

private theorem descended_section_projection {C : Type*} [Category* C]
    {V W B I J Fi Fj G : C}
    (a : V ⟶ B) (e : B ⟶ I) (pi : I ⟶ G) (pj : B ⟶ J) (qj : J ⟶ G)
    (u : V ⟶ W) (sj : W ⟶ J) (lj : W ⟶ Fj) (cj : Fj ⟶ G)
    (li : V ⟶ Fi) (t : Fi ⟶ Fj) (ci : Fi ⟶ G) (si : V ⟶ I)
    (he : e ≫ pi = pj ≫ qj) (hp : a ≫ pj = u ≫ sj)
    (hj : sj ≫ qj = lj ≫ cj) (ht : u ≫ lj = li ≫ t)
    (hc : t ≫ cj = ci) (hi : si ≫ pi = li ≫ ci) :
    (a ≫ e) ≫ pi = si ≫ pi := by
  calc
    _ = (a ≫ pj) ≫ qj := by rw [Category.assoc, he, ← Category.assoc]
    _ = (u ≫ sj) ≫ qj := congrArg (fun k => k ≫ qj) hp
    _ = (u ≫ lj) ≫ cj := by rw [Category.assoc, hj, ← Category.assoc]
    _ = (li ≫ t) ≫ cj := congrArg (fun k => k ≫ cj) ht
    _ = li ≫ ci := by rw [Category.assoc, hc]
    _ = _ := hi.symm

variable {S : Scheme.{u}} (C : S.OpenCover.{u})
  [Category C.I₀] [C.LocallyDirected] [Small.{u} C.I₀] [Quiver.IsThin C.I₀]
  [∀ i, IsLocallyNoetherian (C.X i)] {g N : ℕ} {δ : Fin g → ℕ}
  (F : ∀ i, PolarizationData.PolarizedAbelianWithFullLevel g δ N (C.X i)) (hN : 3 ≤ N)
  (e : ∀ {i j : C.I₀} (f : i ⟶ j), Moduli.Isomorphisms.LevelPreservingIso (F i) ((F j).pullback (C.trans f)))

def localLevel (i : C.I₀) : ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e).pullback (C.f i)).FullLevel N :=
  (F i).level.transport (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i)

theorem localLevel_projection (i : C.I₀)
    (z : Multiplicative (Fin (2 * g) → ZMod N)) :
    ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e).pullback (C.f i)).fullLevelGlobalSection (localLevel C F hN e i) z ≫
        pullback.fst (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e).scheme.hom (C.f i) =
      (F i).abelian.fullLevelGlobalSection (F i).level z ≫
        (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e).chartMap i := by
  have he : (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i).hom.left ≫
      pullback.fst (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e).scheme.hom (C.f i) =
        (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e).chartMap i :=
    (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e).chartIso_fst i
  exact transported_section_projection _ _ _ _ _
    (Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport (F i).level (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) z) he

omit [Small.{u, u} C.I₀] [Quiver.IsThin C.I₀] in
theorem transition_sections {i j : C.I₀} (f : i ⟶ j)
    (z : Multiplicative (Fin (2 * g) → ZMod N)) :
    (F i).abelian.fullLevelGlobalSection (F i).level z ≫
        (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e).transition f =
      C.trans f ≫ (F j).abelian.fullLevelGlobalSection (F j).level z := by
  have hs : (F i).abelian.fullLevelGlobalSection (F i).level z ≫ (e f).abelian.hom.left =
      ((F j).abelian.pullback (C.trans f)).fullLevelGlobalSection
        ((F j).level.pullback (C.trans f)) z :=
    congrArg Over.Hom.left ((e f).level (Over.mk (𝟙 (C.X i))) (LocallyConstant.const (C.X i) z))
  exact section_total_projection _ _ _ _ _ hs
    ((F j).abelian.fullLevelGlobalSection_pullback (F j).level (C.trans f) z)

theorem localLevel_natural {i j : C.I₀} (f : i ⟶ j) :
    ((localLevel C F hN e j).pullback (C.trans f)).transport
      ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e).openCoverParameterIso C f).symm =
        localLevel C F hN e i := by
  let A := PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e
  apply Abelian.Schemes.AbelianScheme.FullLevel.ext_globalSections
  intro z
  apply (cancel_mono (pullback.fst A.scheme.hom (C.f i))).mp
  have hp : (A.openCoverParameterIso C f).inv.left ≫ pullback.fst A.scheme.hom (C.f i) =
      pullback.fst (A.pullback (C.f j)).scheme.hom (C.trans f) ≫
        pullback.fst A.scheme.hom (C.f j) :=
    ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst (FamilyHomGluing.DirectedFamilyHomGluing.testMap C f) A.scheme
  have htr := Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_transport
    ((localLevel C F hN e j).pullback (C.trans f)) (A.openCoverParameterIso C f).symm z
  exact (congrArg (fun s : C.X i ⟶ (A.pullback (C.f i)).scheme.left =>
    s ≫ pullback.fst A.scheme.hom (C.f i)) htr).trans
      (descended_section_projection _ _ _ _ _ _ _ _ _ _ _ _ _ hp
        ((A.pullback (C.f j)).fullLevelGlobalSection_pullback
          (localLevel C F hN e j) (C.trans f) z)
        (localLevel_projection C F hN e j z) (transition_sections C F hN e f z).symm
        ((PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianData C F hN e).chartMap_transition f) (localLevel_projection C F hN e i z))

variable [IsNoetherian S] [NeZero N]

/-- The original full ordered level on the actual glued abelian scheme. -/
def level : (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e).FullLevel N :=
  Abelian.Schemes.AbelianScheme.level (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e) C
    (localLevel C F hN e) (localLevel_natural C F hN e)

theorem level_chart (i : C.I₀) :
    (DirectedPolarizedSchemeGluing.level C F hN e).pullback (C.f i) = localLevel C F hN e i :=
  Abelian.Schemes.AbelianScheme.level_pullback (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelian C F hN e) C
    (localLevel C F hN e) (localLevel_natural C F hN e) i

theorem chartIso_level (i : C.I₀) :
    (F i).level.transport (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) =
      (DirectedPolarizedSchemeGluing.level C F hN e).pullback (C.f i) :=
  (level_chart C F hN e i).symm

theorem chartIso_level_basis (i : C.I₀) (T : Over (C.X i))
    (z : LocallyConstant T.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    ((F i).level.hom.app (.op T) z).val ≫ (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i).hom =
      (((DirectedPolarizedSchemeGluing.level C F hN e).pullback (C.f i)).hom.app (.op T) z).val :=
  ((F i).level.transport_basis (PolarizedSchemeGluing.DirectedPolarizedSchemeGluing.abelianChartIso C F hN e i) T z).symm.trans
    (congrArg (fun l => (l.hom.app (.op T) z).val) (chartIso_level C F hN e i))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.LevelGluing.DirectedPolarizedSchemeGluing
