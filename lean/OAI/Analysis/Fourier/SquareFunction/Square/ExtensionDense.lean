import Mathlib

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.Fourier.SquareFunction

/-- A Lipschitz map on a dense, possibly redundantly indexed core has a
unique continuous extension to the ambient space. No injectivity or
completion of the core is assumed. -/
theorem exists_lipschitz_extension_dense
    {I A B : Type*} [PseudoMetricSpace A] [MetricSpace B] [CompleteSpace B]
    (i : I → A) (hi : DenseRange i) (f : I → B) (C : NNReal)
    (hf : ∀ x y, dist (f x) (f y) ≤ C * dist (i x) (i y)) :
    ∃ F : A → B, LipschitzWith C F ∧ (∀ x, F (i x) = f x) ∧
      ∀ G : A → B, Continuous G → (∀ x, G (i x) = f x) → G = F := by
  let g : Set.range i → B := fun x => f x.property.choose
  have hg (x : I) : g ⟨i x,⟨x,rfl⟩⟩ = f x := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    simpa only [g, (show i (Exists.choose (show ∃ y, i y = i x from ⟨x,rfl⟩)) = i x from
      Exists.choose_spec (show ∃ y, i y = i x from ⟨x,rfl⟩)),dist_self,mul_zero] using
      hf (Exists.choose (show ∃ y, i y = i x from ⟨x,rfl⟩)) x
  have hglip : LipschitzWith C g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [g,x.property.choose_spec,y.property.choose_spec,Subtype.dist_eq] using
      hf x.property.choose y.property.choose
  let F := hi.extend g
  have hc : Continuous F := (hi.uniformContinuous_extend hglip.uniformContinuous).continuous
  have hFi (x : I) : F (i x) = f x :=
    (hi.extend_of_ind hglip.uniformContinuous ⟨i x,⟨x,rfl⟩⟩).trans (hg x)
  have hF : LipschitzWith C F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    refine hi.induction_on₂ ?_ ?_ x y
    · exact isClosed_le (hc.fst'.dist hc.snd')
        (continuous_const.mul (continuous_fst.dist continuous_snd))
    · intro a b
      rw [hFi,hFi]
      exact hf a b
  refine ⟨F,hF,hFi,?_⟩
  intro G hG hGi
  funext x
  exact hi.induction_on x (isClosed_eq hG hc) (fun a => (hGi a).trans (hFi a).symm)

end OAI.Analysis.Fourier.SquareFunction
