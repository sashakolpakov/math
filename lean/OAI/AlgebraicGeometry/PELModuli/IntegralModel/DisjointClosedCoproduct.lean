import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits

/-! # Disjoint Closed Coproduct -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointClosedCoproduct

noncomputable section

/-! Finitely many disjoint closed immersions form a closed immersion
from their actual scheme coproduct. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.Topology

variable {I : Type} [Finite I] {X : I → Scheme.{0}} {Y : Scheme.{0}}
    (f : ∀ i, X i ⟶ Y) [∀ i, IsClosedImmersion (f i)]

theorem finite_disjoint_closed_sigmaDesc
    (hd : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))) :
    IsClosedImmersion (Sigma.desc f) := by
  have : SurjectiveOnStalks (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) (fun i => inferInstance)
  have hinj : Function.Injective (Sigma.desc f) := by
    intro x y h
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
    obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk X).surjective y
    simp only [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] at h ⊢
    obtain rfl : i = j := by
      by_contra hij
      exact Set.disjoint_left.mp (hd hij) (Set.mem_range_self x) ⟨y, h.symm⟩
    exact congrArg (Sigma.ι X i) ((f i).isClosedEmbedding.injective h)
  have hc : IsClosedMap (Sigma.desc f) := by
    intro Z hZ
    have him : (Sigma.desc f) '' Z = ⋃ i, (f i) '' ((Sigma.ι X i) ⁻¹' Z) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
        refine Set.mem_iUnion.mpr ⟨i, x, ?_, ?_⟩
        · change Sigma.ι X i x ∈ Z
          simpa only [sigmaMk_mk] using hx
        · simp only [sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
      · intro hy
        obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
        exact ⟨Sigma.ι X i x, hx, by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
    rw [him]
    exact isClosed_iUnion_of_finite (fun i => (f i).isClosedEmbedding.isClosedMap _
      (hZ.preimage (Sigma.ι X i).continuous))
  exact ⟨IsClosedEmbedding.of_continuous_injective_isClosedMap (Sigma.desc f).continuous hinj hc⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointClosedCoproduct
