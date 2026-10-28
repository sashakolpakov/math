import Mathlib

/-! # Dense Additive Completion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAdditiveCompletion.TestTransport

noncomputable section

/-! Comparing complete additive groups through the same dense rational
group and its actual zero-neighborhood filter. -/

open scoped _root_.Topology
open Filter

variable {A X Y : Type*} [AddCommGroup A]
  [AddCommGroup X] [UniformSpace X] [IsUniformAddGroup X]
  [AddCommGroup Y] [UniformSpace Y] [IsUniformAddGroup Y]

theorem additive_comap_uniformity_eq
    (i : A →+ X) (j : A →+ Y)
    (h : comap i (𝓝 (0 : X)) = comap j (𝓝 (0 : Y))) :
    (inferInstance : UniformSpace X).comap i =
      (inferInstance : UniformSpace Y).comap j := by
  apply IsUniformAddGroup.ext (.comap i) (.comap j)
  simpa only [UniformSpace.toTopologicalSpace_comap, nhds_induced, map_zero] using h

theorem exists_additive_completion_homeomorph
    [CompleteSpace X] [T2Space X] [CompleteSpace Y] [T2Space Y]
    (i : A →+ X) (j : A →+ Y) (hi : DenseRange i) (hj : DenseRange j)
    (h : comap i (𝓝 (0 : X)) = comap j (𝓝 (0 : Y))) :
    ∃ e : X ≃ₜ Y, (∀ a, e (i a) = j a) ∧ ∀ x y, e (x + y) = e x + e y := by
  let : UniformSpace A := (inferInstance : UniformSpace X).comap i
  let px : AbstractCompletion A :=
    { space := X
      coe := i
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := ⟨rfl⟩
      dense := hi }
  let py : AbstractCompletion A :=
    { space := Y
      coe := j
      uniformStruct := inferInstance
      complete := inferInstance
      separation := inferInstance
      isUniformInducing := by
        constructor
        exact congrArg (fun u : UniformSpace A => @UniformSpace.uniformity A u)
          (additive_comap_uniformity_eq i j h).symm
      dense := hj }
  let e : X ≃ₜ Y := (px.compareEquiv py).toHomeomorph
  have he (a : A) : e (i a) = j a := px.compare_coe py a
  refine ⟨e, he, ?_⟩
  have hadd : (fun p : X × X => e (p.1 + p.2)) =
      (fun p : X × X => e p.1 + e p.2) := by
    apply (hi.prodMap hi).equalizer
      (e.continuous.comp (continuous_fst.add continuous_snd))
      ((e.continuous.comp continuous_fst).add (e.continuous.comp continuous_snd))
    funext p
    change e (i p.1 + i p.2) = e (i p.1) + e (i p.2)
    rw [← map_add, he, he, he, map_add]
  exact fun x y => congr_fun hadd (x, y)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseAdditiveCompletion.TestTransport
