import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homotopy.Lifting

/-! # Continuous Square Root -/

namespace OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

noncomputable section

/-! Parameter-continuous square roots on convex domains. The prescribed
root at one point is transported by the square covering along straight
segments; no connectedness of the parameter space is required. -/

open scoped Classical unitInterval

theorem continuous_square_roots_eq {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hn : ∀ x, f x ≠ 0) (hs : ∀ x, f x ^ 2 = g x ^ 2)
    (x₀ : X) (h₀ : f x₀ = g x₀) : f = g := by
  let s : Set ℂ := {0}ᶜ
  let p : ℂ → ℂ := fun z => z ^ 2
  have cov : IsCoveringMap (s.restrictPreimage p) :=
    (isCoveringMapOn_npow (𝕜 := ℂ) 2 (by norm_num)).isCoveringMap_restrictPreimage
  have hfn (x : X) : p (f x) ∈ s := pow_ne_zero _ (hn x)
  have hgn (x : X) : p (g x) ∈ s := by
    change g x ^ 2 ≠ 0
    rw [← hs x]
    exact hfn x
  let F : X → p ⁻¹' s := fun x => ⟨f x, hfn x⟩
  let G : X → p ⁻¹' s := fun x => ⟨g x, hgn x⟩
  have he : F = G := cov.eq_of_comp_eq (hf.subtype_mk _) (hg.subtype_mk _) (by
    funext x
    exact Subtype.ext (hs x)) x₀ (Subtype.ext h₀)
  exact funext (fun x => congrArg Subtype.val (congrFun he x))

theorem parameter_square_root {G V : Type*} [TopologicalSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Set V) (hs : Convex ℝ s) (z₀ : s)
    (f : G × s → ℂ) (hf : Continuous f) (hn : ∀ p, f p ≠ 0)
    (a : G → ℂ) (ha : Continuous a) (has : ∀ g, a g ^ 2 = f (g, z₀)) :
    ∃ J : G × s → ℂ, Continuous J ∧
      (∀ p, J p ^ 2 = f p) ∧ (∀ g, J (g, z₀) = a g) := by
  let segment : unitInterval × s → s := fun q =>
    ⟨(1 - (q.1 : ℝ)) • z₀.val + (q.1 : ℝ) • q.2.val,
      hs z₀.property q.2.property (sub_nonneg.mpr q.1.property.2) q.1.property.1 (by ring)⟩
  have hc : Continuous segment := by fun_prop
  have hzero (z : s) : segment (0, z) = z₀ := by
    apply Subtype.ext
    simp [segment]
  have hone (z : s) : segment (1, z) = z := by
    apply Subtype.ext
    simp [segment]
  have hfixed (t : unitInterval) : segment (t, z₀) = z₀ := by
    apply Subtype.ext
    change (1 - (t : ℝ)) • z₀.val + (t : ℝ) • z₀.val = z₀.val
    rw [← add_smul, sub_add_cancel, one_smul]
  let nz : Set ℂ := {0}ᶜ
  let p : ℂ → ℂ := fun z => z ^ 2
  have cov : IsCoveringMap (nz.restrictPreimage p) :=
    (isCoveringMapOn_npow (𝕜 := ℂ) 2 (by norm_num)).isCoveringMap_restrictPreimage
  let H : C(unitInterval × (G × s), nz) :=
    ⟨fun q => ⟨f (q.2.1, segment (q.1, q.2.2)), hn _⟩,
      (hf.comp (continuous_snd.fst.prodMk (hc.comp
        (continuous_fst.prodMk continuous_snd.snd)))).subtype_mk _⟩
  have han (g : G) : a g ^ 2 ≠ 0 := by rw [has]; exact hn _
  let initial : C(G × s, p ⁻¹' nz) :=
    ⟨fun q => ⟨a q.1, han q.1⟩, (ha.comp continuous_fst).subtype_mk _⟩
  have hstart (q : G × s) : H (0, q) = nz.restrictPreimage p (initial q) := by
    apply Subtype.ext
    change f (q.1, segment (0, q.2)) = a q.1 ^ 2
    rw [hzero, has]
  let lift := cov.liftHomotopy H initial hstart
  have hlift (t : unitInterval) (q : G × s) :
      (lift (t, q)).val ^ 2 = f (q.1, segment (t, q.2)) :=
    congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H initial hstart) (t, q))
  have hliftzero (q : G × s) : (lift (0, q)).val = a q.1 :=
    congrArg Subtype.val (cov.liftHomotopy_zero H initial hstart q)
  refine ⟨fun q => (lift (1, q)).val, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (lift.continuous.comp (continuous_const.prodMk continuous_id))
  · intro q
    rw [hlift, hone]
  · intro g
    have he := continuous_square_roots_eq
      (fun t : unitInterval => (lift (t, (g, z₀))).val) (fun _ => a g)
      (continuous_subtype_val.comp (lift.continuous.comp (continuous_id.prodMk continuous_const)))
      continuous_const (fun t h => by
        have hn' := han g
        rw [has, ← hfixed t, ← hlift t (g, z₀), h] at hn'
        exact hn' (by norm_num))
      (fun t => by rw [hlift, hfixed, has]) 0 (hliftzero (g, z₀))
    exact congrFun he 1

end

end OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot
