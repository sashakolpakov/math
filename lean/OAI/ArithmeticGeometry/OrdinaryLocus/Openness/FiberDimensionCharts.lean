import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SmoothDimensionCharts
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Fiber Dimension Charts -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction

noncomputable section

/-! Reading the dimension of a group fiber from any smooth chart it meets. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- A geometric group fiber meeting an open chart of relative dimension n
has dimension n. Translations identify the dimension at its closed points. -/
theorem dimension_fiber_of_smooth_chart
    {S : Scheme.{u}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (i : B ⟶ A) [IsOpenImmersion i.left] (n : ℕ)
    [SmoothOfRelativeDimension n B.hom] (s : S) (hs : s ∈ Set.range B.hom) :
    topologicalKrullDim (A.hom.fiber s) = (n : WithBot ℕ∞) := by
  let K := AlgebraicClosure (S.residueField s)
  let t : Spec (CommRingCat.of K) ⟶ S := (DefinitionsTorsion.geometricPoint S s).hom
  let F := Over.pullback t
  let G := F.obj A
  let C := F.obj B
  let j : C ⟶ G := F.map i
  have : Smooth G.hom := by change Smooth (pullback.snd A.hom t); infer_instance
  have : IsProper G.hom := by change IsProper (pullback.snd A.hom t); infer_instance
  have : GeometricallyConnected G.hom := by
    change GeometricallyConnected (pullback.snd A.hom t)
    infer_instance
  have : IsOpenImmersion j.left :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) t i inferInstance
  have hbase : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have : SmoothOfRelativeDimension n C.hom := by
    change SmoothOfRelativeDimension n (pullback.snd B.hom t)
    exact @MorphismProperty.of_isPullback _ _ (@SmoothOfRelativeDimension.{u} n) hbase
      _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback B.hom t) inferInstance
  have : Smooth C.hom := SmoothOfRelativeDimension.smooth n C.hom
  have : JacobsonSpace C.left := LocallyOfFiniteType.jacobsonSpace C.hom
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : Nonempty C.left := by
    obtain ⟨b, hb⟩ := hs
    let k : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
    have hbk : B.hom b = t k := hb.trans (S.fromSpecResidueField_apply s _).symm
    obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback b k hbk
    exact ⟨z⟩
  obtain ⟨c, _, hc⟩ := nonempty_inter_closedPoints
    (X := C.left) Set.univ_nonempty isOpen_univ.isLocallyClosed
  have hjc : IsClosed {j.left c} := by
    change c ∈ j.left ⁻¹' closedPoints G.left
    rw [j.left.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have hdim : topologicalKrullDim G.left = ringKrullDim (C.left.presheaf.stalk c) := by
    rw [GroupDimension.Construction.topologicalKrullDim_eq_stalk_of_transitive_closedPoints G.left (fun x y hx hy => by
      obtain ⟨α, _, hxy, _⟩ := FlatTranslations.Construction.multiplication_transitive_automorphisms G 1 x y hx hy
      exact ⟨α, hxy⟩) (j.left c) hjc,
      ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight,
      coheight_eq_of_isOpenImmersion j.left]
  exact (GeometricDimension.Construction.topologicalKrullDim_geometricFiber A s).symm.trans
    (hdim.trans (SmoothRelativeDimension.Construction.ringKrullDim_stalk_of_smoothOfRelativeDimension n C.hom c hc))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberDimensionCharts.Construction
