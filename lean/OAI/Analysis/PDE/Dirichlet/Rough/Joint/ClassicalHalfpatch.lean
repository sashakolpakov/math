import OAI.Analysis.PDE.Dirichlet.Rough.Joint.ChartClassicalJets
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.MooreHalfpatch

noncomputable section
open Set Filter
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace
attribute [local instance] residualFirstGroup residualFirstSpace
  residualSecondGroup residualSecondSpace

variable {m n : ℕ} {Z E X : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "W" => EuclideanSpace ℝ (Fin m)
local notation "Phys" => CoordinateSpace n 4

/-- Apply the joint normal bootstrap using equations for the actual
classical spatial slices. The only jointly C² function needed is the
already constructed representative; its boundary jets are identified by
density, not imposed as an additional regularity assumption. -/
theorem exists_smooth_joint_classical_halfpatch
    (e : W ≃L[ℝ] Z × X) (k : X →L[ℝ] ℝ)
    (Bg : Z × X → Phys →L[ℝ] Phys →L[ℝ] ℝ)
    (J : Z × X → Phys →L[ℝ] X)
    (T : Z × X → Phys →L[ℝ] Phys →L[ℝ] X) (load : Z × X → ℝ)
    (hBg : ContDiff ℝ ∞ Bg) (hJ : ContDiff ℝ ∞ J)
    (hT : ContDiff ℝ ∞ T) (hload : ContDiff ℝ ∞ load)
    (ν : W) (hν : (k.comp (reindexSpatialProjection e)) ν = 1)
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) (hKΩ : K ⊆ closure Ω)
    {S : Set Z} {F : Z × E → ℝ}
    (hF : ∀ z ∈ S, ∀ x ∈ K, ContDiffAt ℝ 2 (fun y => F (z,y)) x)
    {g : Z × E → ℝ} (hg : ContDiff ℝ 2 g)
    (he : ∀ z ∈ S, ∀ x ∈ K, g (z,x) = F (z,x))
    (G : X → E) (hG : ContDiff ℝ ∞ G)
    {O : Set W} (hO : IsOpen O) {Q : Set (Z × X)}
    (hmaps : MapsTo e ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) Q)
    (hQ : ∀ p ∈ Q, p.1 ∈ S ∧ G p.2 ∈ K)
    (hi : ∀ x ∈ O, 0 < (k.comp (reindexSpatialProjection e)) x →
      ContDiffAt ℝ ∞ (fun y : W => F ((e y).1,G (e y).2)) x)
    (hmixed : ∀ (N : ℕ) (v : Fin N → Z × k.ker),
      ContDiffOn ℝ 2 (fun p : Z × X ↦ iteratedFDeriv ℝ N
        (fun t : Z × k.ker ↦ F (p.1+t.1,G (p.2+(t.2:X)))) 0 v) Q)
    (honto : ∀ p ∈ Q, Function.Surjective (J p))
    (hpositive : ∀ p ∈ Q,
      (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg p) (J p) (T p)
        (fderiv ℝ (fun y => F (p.1,G y)) p.2)
        (fderiv ℝ (fderiv ℝ (fun y => F (p.1,G y))) p.2))).PosDef)
    (heq : ∀ p ∈ Q,
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg p) (J p) (T p)
        (fderiv ℝ (fun y => F (p.1,G y)) p.2)
        (fderiv ℝ (fderiv ℝ (fun y => F (p.1,G y))) p.2)) = load p)
    {x₀ : W} (hx₀ : x₀ ∈ O) (hxk : (k.comp (reindexSpatialProjection e)) x₀ = 0) :
    ∃ V : Set W, IsOpen V ∧ x₀ ∈ V ∧ V ⊆ O ∧
      ∃ u : W → ℝ, ContDiff ℝ ∞ u ∧
        EqOn u (fun y => F ((e y).1,G (e y).2))
          ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ V) := by
  let g' : W → ℝ := fun y => g ((e y).1,G (e y).2)
  have hg' : ContDiff ℝ 2 g' :=
    hg.comp ((contDiff_fst.prodMk ((hG.of_le (by simp)).comp contDiff_snd)).comp e.contDiff)
  have he' : EqOn g' ((fun p : Z × X => F (p.1,G p.2)) ∘ e)
      ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O) := by
    intro x hx
    obtain ⟨hz,hxK⟩ := hQ (e x) (hmaps hx)
    exact he (e x).1 hz (G (e x).2) hxK
  have hj (x : W) (hx : x ∈ ({x | 0 ≤ (k.comp (reindexSpatialProjection e)) x} ∩ O)) :
      spatialGradientRestriction (reindexSpatialInclusion e) (fderiv ℝ g' x) =
        fderiv ℝ (fun y => F ((e x).1,G y)) (e x).2 ∧
      spatialHessianRestriction (reindexSpatialInclusion e) (fderiv ℝ (fderiv ℝ g') x) =
        fderiv ℝ (fderiv ℝ (fun y => F ((e x).1,G y))) (e x).2 := by
    obtain ⟨hz,hxK⟩ := hQ (e x) (hmaps hx)
    have hh := parameterJetProjection_of_classical_chart e hΩ hΩK hKΩ hF hg he
      (hG.of_le (by simp)) x hz hxK
    exact ⟨congrArg (fun a : Z × NonlinearJet X => a.2.1.2) hh,
      congrArg (fun a : Z × NonlinearJet X => a.2.2) hh⟩
  apply exists_smooth_joint_moore_halfpatch e k Bg J T load hBg hJ hT hload ν hν
    hO hg' he' hmaps ?_ hmixed ?_ ?_ ?_ hx₀ hxk
  · intro x hx hpos
    apply (hi x hx hpos).congr_of_eventuallyEq
    have hposopen : IsOpen {y : W | 0 < (k.comp (reindexSpatialProjection e)) y} :=
      isOpen_lt continuous_const (k.comp (reindexSpatialProjection e)).continuous
    filter_upwards [hO.mem_nhds hx,hposopen.mem_nhds hpos] with y hy hyp
    exact he' ⟨hyp.le,hy⟩
  · exact fun x hx => honto (e x) (hmaps hx)
  · intro x hx
    rw [(hj x hx).1,(hj x hx).2]
    exact hpositive (e x) (hmaps hx)
  · intro x hx
    rw [(hj x hx).1,(hj x hx).2]
    exact heq (e x) (hmaps hx)

end OAI.Analysis.PDE.Dirichlet
