import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ComparisonRestriction
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.OpenLineOverlap
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomDescended
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Local Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocalDescent

noncomputable section

section

/-! Actual quotient covers supply local descent solutions on a common
frame cover of the two line bundles. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

theorem line_quotient_basechange_geometry {S : Scheme.{0}} {X Y U : Over S}
    (f : X ⟶ Y) (i : U ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    IsFinite (pullback.snd f i).left ∧ Etale (pullback.snd f i).left ∧
      Surjective (pullback.snd f i).left := by
  have h := (Over.forget S).map_isPullback (IsPullback.of_hasPullback f i)
  exact ⟨MorphismProperty.of_isPullback h ‹IsFinite f.left›,
    MorphismProperty.of_isPullback h ‹Etale f.left›,
    MorphismProperty.of_isPullback h ‹Surjective f.left›⟩

theorem line_quotient_basechange_effective {S : Scheme.{0}} {X Y U : Over S}
    (f : X ⟶ Y) (i : U ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left] :
    EffectiveEpi (pullback.snd f i).left := by
  obtain ⟨hf, he, hs⟩ := line_quotient_basechange_geometry f i
  infer_instance

def LineLocalDescentEquation {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left)
    (a : (L.pullback f.left).sheaf ≅ (M.pullback f.left).sheaf)
    (U : Y.left.Opens)
    (d : (L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf) : Prop :=
  let i := OpenLineOverlap.Construction.lineOpenInclusion Y U
  let p := pullback.fst f i
  let r := pullback.snd f i
  pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L.sheaf) (M₂ := M.sheaf)
      (f₁ := i) (f₂ := i) d.hom r (r ≫ i) (r ≫ i) rfl rfl =
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L.sheaf) (M₂ := M.sheaf)
      (f₁ := f) (f₂ := f) a.hom p (r ≫ i) (r ≫ i) pullback.condition pullback.condition

theorem exists_line_local_descent {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left) :
    let F := LinePullHom.Construction.overSchemeModulePullbacks S
    ∀ a : (F.map f.op.toLoc).toFunctor.obj L.sheaf ≅
        (F.map f.op.toLoc).toFunctor.obj M.sheaf,
      (∀ (T : Over S) (s t : T ⟶ X) (w : T ⟶ Y) (hs : s ≫ f = w) (ht : t ≫ f = w),
        pullHom (F := F) a.hom s w w hs hs = pullHom (F := F) a.hom t w w ht ht) →
      ∀ (U : Y.left.Opens), Nonempty ((L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf) →
      ∃ d : (L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf,
        LineLocalDescentEquation f L M a U d := by
  dsimp only
  intro a ha U ⟨b⟩
  let i := OpenLineOverlap.Construction.lineOpenInclusion Y U
  obtain ⟨hf, he, hs⟩ := line_quotient_basechange_geometry f i
  have hE := line_quotient_basechange_effective f i
  exact ComparisonRestriction.Construction.comparison_desc_on_base f i (pullback.fst f i) (pullback.snd f i)
    pullback.condition L M b a ha

theorem common_line_frame_cover {Y : Scheme.{0}} (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (x : Y) :
    ∃ U : Y.Opens, x ∈ U ∧ Nonempty ((L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf) := by
  obtain ⟨U, hxU, ⟨l⟩⟩ := L.locallyTrivial x
  obtain ⟨V, hxV, ⟨m⟩⟩ := M.locallyTrivial x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩,
    ⟨L.frameRestrict inf_le_left l ≪≫ (M.frameRestrict inf_le_right m).symm⟩⟩

end Construction

end

section

/-! Local solutions agree on every smaller open because their pullbacks
to the actual quotient cover agree with the same original comparison. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

def LineRestrictionOnCover {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left)
    (a : (L.pullback f.left).sheaf ≅ (M.pullback f.left).sheaf)
    (U W : Y.left.Opens) (hW : W ≤ U)
    (d : (L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf) : Prop :=
  let i := OpenLineOverlap.Construction.lineOpenInclusion Y W
  let p := pullback.fst f i
  let r := pullback.snd f i
  pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L.sheaf) (M₂ := M.sheaf)
      (f₁ := i) (f₂ := i) (OpenLineOverlap.Construction.lineOpenPullHom Y L.sheaf M.sheaf U W hW d.hom)
      r (r ≫ i) (r ≫ i) rfl rfl =
    pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L.sheaf) (M₂ := M.sheaf)
      (f₁ := f) (f₂ := f) a.hom p (r ≫ i) (r ≫ i) pullback.condition pullback.condition

theorem line_local_solution_restrict {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left)
    (a : (L.pullback f.left).sheaf ≅ (M.pullback f.left).sheaf)
    (U W : Y.left.Opens) (hW : W ≤ U)
    (d : (L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf)
    (hd : LineLocalDescentEquation f L M a U d) :
    LineRestrictionOnCover f L M a U W hW d := by
  let F := LinePullHom.Construction.overSchemeModulePullbacks S
  let iU := OpenLineOverlap.Construction.lineOpenInclusion Y U
  let iW := OpenLineOverlap.Construction.lineOpenInclusion Y W
  let j := OpenLineOverlap.Construction.lineOpenSubinclusion Y hW
  let pU := pullback.fst f iU
  let rU := pullback.snd f iU
  let pW := pullback.fst f iW
  let rW := pullback.snd f iW
  have hj : j ≫ iU = iW := OpenLineOverlap.Construction.lineOpenSubinclusion_comp Y hW
  have ht : pW ≫ f = (rW ≫ j) ≫ iU := by
    rw [Category.assoc, hj]
    exact pullback.condition
  let t := pullback.lift pW (rW ≫ j) ht
  dsimp only [LineRestrictionOnCover, OpenLineOverlap.Construction.lineOpenPullHom]
  rw [pullHom_pullHom]
  apply PullHomDescended.Construction.pullHom_descended_transport F f iU pU rU pullback.condition a.hom d.hom hd
    t (rW ≫ j) pW (rW ≫ iW)
  · exact pullback.lift_snd _ _ _
  · exact pullback.lift_fst _ _ _

theorem lineOpenPullHom_isIso {S : Scheme.{0}} (Y : Over S) (L M : Y.left.Modules)
    (U W : Y.left.Opens) (hW : W ≤ U)
    (d : (Scheme.Modules.pullback U.ι).obj L ≅ (Scheme.Modules.pullback U.ι).obj M) :
    IsIso (OpenLineOverlap.Construction.lineOpenPullHom Y L M U W hW d.hom) := by
  let F := LinePullHom.Construction.overSchemeModulePullbacks S
  exact PullHomNormalization.Construction.pullHom_isIso F (L := L) (M := M)
    (x := OpenLineOverlap.Construction.lineOpenInclusion Y U) (y := OpenLineOverlap.Construction.lineOpenInclusion Y U) d.hom
    (OpenLineOverlap.Construction.lineOpenSubinclusion Y hW) (OpenLineOverlap.Construction.lineOpenInclusion Y W) (OpenLineOverlap.Construction.lineOpenInclusion Y W)
    (OpenLineOverlap.Construction.lineOpenSubinclusion_comp Y hW) (OpenLineOverlap.Construction.lineOpenSubinclusion_comp Y hW)

theorem line_local_solutions_agree {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left)
    (a : (L.pullback f.left).sheaf ≅ (M.pullback f.left).sheaf)
    (U V W : Y.left.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (d : (L.pullback U.ι).sheaf ≅ (M.pullback U.ι).sheaf)
    (e : (L.pullback V.ι).sheaf ≅ (M.pullback V.ι).sheaf)
    (hd : LineLocalDescentEquation f L M a U d)
    (he : LineLocalDescentEquation f L M a V e) :
    OpenLineOverlap.Construction.lineOpenPullHom Y L.sheaf M.sheaf U W hU d.hom =
      OpenLineOverlap.Construction.lineOpenPullHom Y L.sheaf M.sheaf V W hV e.hom := by
  let iW := OpenLineOverlap.Construction.lineOpenInclusion Y W
  let rW := pullback.snd f iW
  have hE := line_quotient_basechange_effective f iW
  have hInj : Function.Injective rW.left.appTop := FunctionDescent.Construction.appTop_injective_of_epi rW.left
  have hIso : IsIso (OpenLineOverlap.Construction.lineOpenPullHom Y L.sheaf M.sheaf U W hU d.hom) :=
    lineOpenPullHom_isIso Y L.sheaf M.sheaf U W hU d
  apply @LinePullHom.Construction.linePullHom_ext S Y (OpenLineOverlap.Construction.lineOpenOver Y W) (pullback f iW) iW rW (rW ≫ iW) rfl
    hInj L M _ _ hIso
  exact (line_local_solution_restrict f L M a U W hU d hd).trans
    (line_local_solution_restrict f L M a V W hV e he).symm

end Construction

end

/-! A compatible comparison of actual line bundles descends through a
finite etale surjective map. The proof constructs local comparisons,
proves their overlap equations, and glues their module isomorphisms. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

theorem compatible_line_iso_desc {S : Scheme.{0}} {X Y : Over S}
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left) :
    let F := LinePullHom.Construction.overSchemeModulePullbacks S
    ∀ a : (F.map f.op.toLoc).toFunctor.obj L.sheaf ≅
        (F.map f.op.toLoc).toFunctor.obj M.sheaf,
      (∀ (T : Over S) (s t : T ⟶ X) (w : T ⟶ Y) (hs : s ≫ f = w) (ht : t ≫ f = w),
        pullHom (F := F) a.hom s w w hs hs = pullHom (F := F) a.hom t w w ht ht) →
      Nonempty (L.sheaf ≅ M.sheaf) := by
  dsimp only
  intro a ha
  choose U hxU hU using common_line_frame_cover L M
  choose d hd using fun x => exists_line_local_descent f L M a ha (U x) (hU x)
  obtain ⟨e, _⟩ := LocalLineIsoGluing.Construction.local_module_isos_glue L.sheaf M.sheaf U
    (fun x => ⟨x, hxU x⟩) (fun x => UnitLocalIsos.Construction.unitLocalLineIsoOver L.sheaf M.sheaf (U x) (d x))
    (fun x y W hW₁ hW₂ => OpenLineOverlap.Construction.unitLocalLineIsoOver_overlap Y L.sheaf M.sheaf (U x) (U y) W
      hW₁ hW₂ (d x) (d y)
        (line_local_solutions_agree f L M a (U x) (U y) W hW₁ hW₂ (d x) (d y) (hd x) (hd y)))
  exact ⟨e⟩

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocalDescent
