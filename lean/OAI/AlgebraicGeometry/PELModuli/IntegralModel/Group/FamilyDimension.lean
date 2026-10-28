import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothDimensionCharts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.LocalDimension
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import OAI.AlgebraicGeometry.Betti.SmoothDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension

/-! # Family Dimension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension

noncomputable section

/-! Dimension of arbitrary algebraically closed fibers meeting a specified
smooth chart. These comparisons apply to transcendental complex points as
well as arithmetic specializations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension

/-- The intrinsic transcendence dimension agrees with the topological
dimension of a smooth proper connected group in characteristic zero. -/
theorem group_krullDim_eq_transcendenceDimension
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [IsIntegral A.left] :
    topologicalKrullDim A.left = (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom : WithBot ℕ∞) := by
  let d := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom
  have : SmoothOfRelativeDimension d A.hom := by
    dsimp [d]
    rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension]
    exact Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (X := A.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  rw [LocalDimension.DimensionSupport.topologicalKrullDim_eq_stalk_of_transitive_closedPoints A.left
    (LocalDimension.DimensionSupport.closed_point_translations A) x hx]
  exact SmoothRelativeDimension.DimensionSupport.ringKrullDim_stalk_of_smoothOfRelativeDimension d A.hom x hx

/-- A nonempty open chart of dimension n computes the dimension of any
algebraically closed fiber it meets, without restricting the field extension
to an algebraic one. -/
theorem dimension_algClosed_baseChange_of_smooth_chart
    {S : Scheme} (A B : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (i : B ⟶ A) [IsOpenImmersion i.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom]
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S)
    (ht : t (IsLocalRing.closedPoint K) ∈ Set.range B.hom) :
    topologicalKrullDim ((Over.pullback t).obj A).left = (n : WithBot ℕ∞) := by
  let F := Over.pullback t
  let G := F.obj A
  let C := F.obj B
  let j : C ⟶ G := F.map i
  have : Smooth G.hom := inferInstanceAs (Smooth (pullback.snd A.hom t))
  have : IsProper G.hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : GeometricallyConnected G.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t))
  have : IsOpenImmersion j.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) t i inferInstance
  have hbase : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have : SmoothOfRelativeDimension n C.hom := by
    change SmoothOfRelativeDimension n (pullback.snd B.hom t)
    exact @MorphismProperty.of_isPullback _ _ (@SmoothOfRelativeDimension n) hbase
      _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback B.hom t) inferInstance
  have : Smooth C.hom := SmoothOfRelativeDimension.smooth n C.hom
  have : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : Nonempty C.left := by
    obtain ⟨b, hb⟩ := ht
    obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := B.hom) (g := t) b (IsLocalRing.closedPoint K) hb
    exact ⟨z⟩
  obtain ⟨c, _, hc⟩ := nonempty_inter_closedPoints
    (X := C.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hjc : IsClosed {j.left c} := by
    change c ∈ j.left ⁻¹' closedPoints G.left
    rw [j.left.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have hd : topologicalKrullDim G.left = ringKrullDim (C.left.presheaf.stalk c) := by
    rw [LocalDimension.DimensionSupport.topologicalKrullDim_eq_stalk_of_transitive_closedPoints G.left
      (LocalDimension.DimensionSupport.closed_point_translations G) (j.left c) hjc,
      ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      coheight_eq_of_isOpenImmersion j.left]
  exact hd.trans (SmoothRelativeDimension.DimensionSupport.ringKrullDim_stalk_of_smoothOfRelativeDimension n C.hom c hc)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.FamilyDimension
