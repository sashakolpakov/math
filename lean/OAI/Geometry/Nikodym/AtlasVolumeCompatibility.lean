import OAI.Geometry.Nikodym.AtlasVolumeCompatibilityMetric
import OAI.Geometry.Nikodym.Abstract.Volume
import OAI.Geometry.Nikodym.Riemannian.VolumeMap

noncomputable section
open Set _root_.MeasureTheory Manifold Bundle
open scoped ContDiff

namespace OAI.Geometry.Nikodym

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]

local notation "𝔼" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓘(ℝ,𝔼)

omit [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓡 n) ∞ M] [RiemannianBundle fun x : M ↦ TangentSpace (𝓡 n) x] [IsContMDiffRiemannianBundle (𝓡 n) ∞ 𝔼 fun x : M ↦ TangentSpace (𝓡 n) x] in
theorem atlasForward_image_eq_extChartAt (p : M) {A : Set M}
    (hA : A ⊆ (extChartAt I p).source) :
    atlasForward (E:=𝔼) p '' A = extChartAt I p '' A := by
  apply image_congr
  exact fun x hx => atlasForward_eq p (hA hx)

/-- The volume assigned to a measurable set in two overlapping ordinary charts
agrees. The proof uses the actual metric pullback and its Jacobian density. -/
theorem atlasRiemannianVolume_eq_on_overlap (p q : M) {A : Set M}
    (hA : MeasurableSet A) (hp : A ⊆ (extChartAt I p).source)
    (hq : A ⊆ (extChartAt I q).source) :
    atlasRiemannianVolume (n:=n) p A = atlasRiemannianVolume (n:=n) q A := by
  let S := extChartAt I p '' A
  have hS : MeasurableSet S := by
    change MeasurableSet (extChartAt I p '' A)
    rw [← atlasForward_image_eq_extChartAt p hp]
    exact measurableSet_atlasForward_image p hA hp
  have hSD : S ⊆ atlasTransitionDomain (E:=𝔼) p q := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨(extChartAt I p).map_source (hp hx), ?_⟩
    change (extChartAt I p).symm (extChartAt I p x) ∈ (extChartAt I q).source
    simpa only [(extChartAt I p).left_inv (hp hx)] using hq hx
  have hFD : MapsTo (atlasTransition (E:=𝔼) p q) S (abstractChartMetric (E:=𝔼) q).domain := by
    intro y hy
    exact (extChartAt I q).map_source (hSD hy).2
  have hder : ∀ y ∈ S, HasFDerivWithinAt (atlasTransition (E:=𝔼) p q)
      (fderiv ℝ (atlasTransition (E:=𝔼) p q) y) S y :=
    fun y hy => (atlasTransition_hasFDerivAt p q (hSD hy)).hasFDerivWithinAt
  have hinj : InjOn (atlasTransition (E:=𝔼) p q) S := by
    rintro y ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩ he
    have he' : extChartAt I q x = extChartAt I q w := by
      simpa only [atlasTransition, Function.comp_apply,
        (extChartAt I p).left_inv (hp hx), (extChartAt I p).left_inv (hp hw)] using he
    exact congrArg (extChartAt I p) ((extChartAt I q).injOn (hq hx) (hq hw) he')
  have hmap := (abstractChartMetric (E:=𝔼) p).map_coordinateVolume_restrict
    (abstractChartMetric (E:=𝔼) q) hS (fun y hy => (hSD hy).1) hFD hder hinj
    (fun y hy u v => abstractChartMetric_transition_inner p q (hSD hy) u v)
  have hi : atlasTransition (E:=𝔼) p q '' S = extChartAt I q '' A := by
    rw [image_image]
    apply image_congr
    intro x hx
    simp only [atlasTransition, Function.comp_apply, (extChartAt I p).left_inv (hp hx)]
  have hm : AEMeasurable (atlasTransition (E:=𝔼) p q)
      ((abstractChartMetric (E:=𝔼) p).coordinateVolume.restrict S) :=
    (show ContinuousOn (atlasTransition (E:=𝔼) p q) S from
      fun y hy => (hder y hy).continuousWithinAt).aemeasurable hS
  have hv := congrArg (fun μ : Measure 𝔼 => μ Set.univ) hmap
  rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ] at hv
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, hi] at hv
  rw [atlasRiemannianVolume_eq_coordinateVolume_image p hA hp,
    atlasRiemannianVolume_eq_coordinateVolume_image q hA hq,
    atlasForward_image_eq_extChartAt p hp, atlasForward_image_eq_extChartAt q hq]
  exact hv

/-- Actual Riemannian atlas measures are compatible on their source overlap. -/
theorem atlasRiemannianVolume_restrict_overlap (p q : M) :
    (atlasRiemannianVolume (n:=n) p).restrict
        ((extChartAt I p).source ∩ (extChartAt I q).source) =
      (atlasRiemannianVolume (n:=n) q).restrict
        ((extChartAt I p).source ∩ (extChartAt I q).source) := by
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact atlasRiemannianVolume_eq_on_overlap p q
    (hA.inter ((isOpen_extChartAt_source p).measurableSet.inter
      (isOpen_extChartAt_source q).measurableSet))
    (fun _ hx => hx.2.1) (fun _ hx => hx.2.2)

end OAI.Geometry.Nikodym
