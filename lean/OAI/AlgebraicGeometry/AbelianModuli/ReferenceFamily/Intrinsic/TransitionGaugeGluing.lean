import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedFrameTransition
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing

/-! # Transition Gauge Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TransitionGaugeGluing

noncomputable section

/-! A literal regular-unit boundary for actual local line-sheaf
frames glues to an actual global trivialization, on any scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem regularUnit_restrict_div {X : Scheme.{0}} {U V : X.Opens}
    (h : V ≤ U) (u v : Γ(X, U)ˣ) :
    RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit h (u / v) =
      RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit h u / RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit h v :=
  map_div (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom) u v

theorem regularUnit_restrict_comp {X : Scheme.{0}} {U V W : X.Opens}
    (h : V ≤ U) (k : W ≤ V) (u : Γ(X, U)ˣ) :
    RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit k (RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit h u) =
      RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit (k.trans h) u := by
  apply Units.ext
  change X.presheaf.map (homOfLE k).op (X.presheaf.map (homOfLE h).op u.val) = _
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

theorem exists_trivialization_of_pair_frame_gauge {X : Scheme.{0}} {M : X.Modules}
    {I : Type} (s : I → LineFrameAtlas.LocalLineFrame M) (hs : iSup (fun i => (s i).domain) = ⊤)
    (r : ∀ i, Γ(X, (s i).domain)ˣ)
    (hr : ∀ i j, (s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right *
      RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit inf_le_left (r i) = RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit inf_le_right (r j)) :
    Nonempty (M ≅ HilbertConstruction.Line.Bundles.structureModule X) := by
  let t (i : I) := Global.FrameTransitions.localFrameOfGlobal (Iso.refl (HilbertConstruction.Line.Bundles.structureModule X)) (s i).domain
  let a (i j : I) : Γ(X, (s i).domain ⊓ (s j).domain) :=
    (s i).transition (s j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right
  let b (i j : I) : Γ(X, (s i).domain ⊓ (s j).domain) :=
    (t i).transition (t j) ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right
  apply RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units M (HilbertConstruction.Line.Bundles.structureModule X) (fun i => (s i).domain) hs
    (fun i => SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization le_rfl (s i).frame)
    (fun i => SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization le_rfl (t i).frame) r a b
  · intro i j
    exact RestrictedFrameTransition.restrictedFrame_transition (s i) (s j) (s i).domain (s j).domain le_rfl le_rfl
  · intro i j
    exact RestrictedFrameTransition.restrictedFrame_transition (t i) (t j) (s i).domain (s j).domain le_rfl le_rfl
  · intro i j
    have hb : b i j = 1 := congrArg Units.val
      (Global.FrameTransitions.localFrameOfGlobal_transition (Iso.refl (HilbertConstruction.Line.Bundles.structureModule X))
        (s i).domain (s j).domain ((s i).domain ⊓ (s j).domain) inf_le_left inf_le_right)
    rw [hb, mul_one]
    exact congrArg Units.val (hr i j)

theorem exists_trivialization_of_cech_frame_gauge {X : Scheme.{0}} {M : X.Modules}
    {I : Type} (s : I → LineFrameAtlas.LocalLineFrame M) (hs : iSup (fun i => (s i).domain) = ⊤)
    (r : ∀ i, Γ(X, (s i).domain)ˣ)
    (hr : ∀ a : Fin 2 → I,
      (s (a 0)).transition (s (a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1) =
      RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1) (r (a 1)) /
      RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0) (r (a 0))) :
    Nonempty (M ≅ HilbertConstruction.Line.Bundles.structureModule X) := by
  apply exists_trivialization_of_pair_frame_gauge s hs r
  intro i j
  let a : Fin 2 → I := Fin.cases i (fun _ => j)
  have h : (s i).domain ⊓ (s j).domain ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun k => (s k).domain) a := by
    apply le_iInf
    intro k
    exact Fin.cases inf_le_left (fun _ => inf_le_right) k
  have hh := congrArg (RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit h) (hr a)
  change Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom _ = _ at hh
  rw [LineFrameAtlas.LocalLineFrame.transition_restrict, regularUnit_restrict_div, regularUnit_restrict_comp,
    regularUnit_restrict_comp] at hh
  exact (congrArg (fun q => q * RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit inf_le_left (r i)) hh).trans
    (div_mul_cancel _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TransitionGaugeGluing
