import OAI.NumberTheory.Quaternion.Arithmetic.PrimeField
import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.NumberTheory.Quaternion.Arithmetic.TangentCone

/-! # Regular Matrix Embedding -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding

noncomputable section

section

/-! A finite-dimensional topological algebra embeds as a closed algebra
of matrices over an extension of its scalar field. This represents an
entire residue-prime block in one normed matrix algebra. -/

open scoped Classical
open _root_.Topology

section

variable {κ K A : Type*} [Field κ] [Field K] [Algebra κ K]
  [Ring A] [Algebra κ A] [FiniteDimensional κ A]

def regularMatrixEmbedding :
    A →ₐ[κ] Matrix (Fin (Module.finrank κ A)) (Fin (Module.finrank κ A)) K :=
  (Algebra.ofId κ K).mapMatrix.comp (Algebra.leftMulMatrix (Module.finBasis κ A))

theorem regularMatrixEmbedding_injective : Function.Injective (regularMatrixEmbedding (κ := κ) (K := K) (A := A)) := by
  intro x y hxy
  apply Algebra.leftMulMatrix_injective (Module.finBasis κ A)
  apply Matrix.map_injective (algebraMap κ K).injective
  exact hxy

end

variable {κ K A : Type*} [NontriviallyNormedField κ] [CompleteSpace κ]
  [NormedField K] [NormedAlgebra κ K]
  [Ring A] [Algebra κ A] [FiniteDimensional κ A]
  [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [ContinuousSMul κ A]

theorem regularMatrixEmbedding_isClosedEmbedding :
    IsClosedEmbedding (regularMatrixEmbedding (κ := κ) (K := K) (A := A)) :=
  LinearMap.isClosedEmbedding_of_injective
    (f := (regularMatrixEmbedding (κ := κ) (K := K) (A := A)).toLinearMap)
    (LinearMap.ker_eq_bot.mpr regularMatrixEmbedding_injective)

end

/-! A closed injective linear representation preserves the actual
tangent cone and tangent span. Finite-dimensionality makes a linear
left inverse continuous. -/

open scoped Classical
open Set Filter _root_.Topology

section

theorem tangentCone_subset_closed_submodule_at
    {κ E : Type*} [Field κ] [AddCommGroup E] [Module κ E] [TopologicalSpace E]
    (W : Submodule κ E) (hW : IsClosed (W : Set E)) {s : Set E} (hs : s ⊆ W)
    {x : E} (hx : x ∈ W) : tangentConeAt κ s x ⊆ (W : Set E) := by
  intro y hy
  obtain ⟨α, l, hl, c, d, hd, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  apply hW.mem_of_tendsto hcd
  filter_upwards [hds] with a ha
  have hm : d a ∈ W := by simpa only [add_sub_cancel_left] using W.sub_mem (hs ha) hx
  exact W.smul_mem (c a) hm

variable {κ E B : Type*} [NontriviallyNormedField κ] [CompleteSpace κ]
  [AddCommGroup E] [Module κ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul κ E]
  [AddCommGroup B] [Module κ B] [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul κ B]
  [T2Space B] [FiniteDimensional κ B]

theorem tangentCone_image_of_closed_linear_embedding
    (f : E →L[κ] B) (hf : IsClosedEmbedding f) (s : Set E) (x : E) :
    tangentConeAt κ (f '' s) (f x) = f '' tangentConeAt κ s x := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨P, hP⟩ := f.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf.injective)
    let p : B →L[κ] E := P.toContinuousLinearMap
    have hp (a : E) : p (f a) = a := LinearMap.congr_fun hP a
    have himage : p '' (f '' s) = s := by
      simp only [image_image, hp, image_id']
    have ht := TangentCone.continuousLinearMap_mapsTo_tangentCone p (f '' s) (f x) hy
    rw [himage, hp] at ht
    have hyr : y ∈ f.toLinearMap.range :=
      tangentCone_subset_closed_submodule_at f.toLinearMap.range hf.isClosed_range
        (fun _ h => by obtain ⟨a, _, rfl⟩ := h; exact ⟨a, rfl⟩) ⟨x, rfl⟩ hy
    obtain ⟨a, ha⟩ := hyr
    refine ⟨p y, ht, ?_⟩
    rw [← ha]
    exact congrArg f (hp a)
  · rintro y ⟨a, ha, rfl⟩
    exact TangentCone.continuousLinearMap_mapsTo_tangentCone f s x ha

theorem tangentSpan_image_of_closed_linear_embedding
    (f : E →L[κ] B) (hf : IsClosedEmbedding f) (s : Set E) (x : E) :
    Submodule.span κ (tangentConeAt κ (f '' s) (f x)) =
      (Submodule.span κ (tangentConeAt κ s x)).map f.toLinearMap := by
  rw [tangentCone_image_of_closed_linear_embedding f hf, Submodule.map_span]
  rfl

theorem tangentSpan_image_mem_iff
    (f : E →L[κ] B) (hf : IsClosedEmbedding f) (s : Set E) (x a : E) :
    f a ∈ Submodule.span κ (tangentConeAt κ (f '' s) (f x)) ↔
      a ∈ Submodule.span κ (tangentConeAt κ s x) := by
  rw [tangentSpan_image_of_closed_linear_embedding f hf, Submodule.mem_map]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact hf.injective hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

end

variable {κ A B : Type*} [NontriviallyNormedField κ] [CompleteSpace κ]
  [Ring A] [Algebra κ A] [TopologicalSpace A] [IsTopologicalRing A]
  [ContinuousSMul κ A] [FiniteDimensional κ A] [T2Space A]
  [Ring B] [Algebra κ B] [TopologicalSpace B] [IsTopologicalRing B]
  [ContinuousSMul κ B] [T2Space B] [FiniteDimensional κ B]

theorem algebraHom_tangentSpan_image (f : A →ₐ[κ] B) (hf : IsClosedEmbedding f) (s : Set A) :
    Submodule.span κ (tangentConeAt κ (f '' s) 1) =
      (Submodule.span κ (tangentConeAt κ s 1)).map f.toLinearMap := by
  let fc : A →L[κ] B := f.toLinearMap.toContinuousLinearMap
  have ht := tangentSpan_image_of_closed_linear_embedding fc hf s 1
  change Submodule.span κ (tangentConeAt κ (f '' s) (f 1)) =
    (Submodule.span κ (tangentConeAt κ s 1)).map f.toLinearMap at ht
  simpa only [map_one] using ht

theorem algebraHom_tangentSpan_image_mem_iff
    (f : A →ₐ[κ] B) (hf : IsClosedEmbedding f) (s : Set A) (a : A) :
    f a ∈ Submodule.span κ (tangentConeAt κ (f '' s) 1) ↔
      a ∈ Submodule.span κ (tangentConeAt κ s 1) := by
  rw [algebraHom_tangentSpan_image f hf, Submodule.mem_map]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact hf.injective hba ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding
