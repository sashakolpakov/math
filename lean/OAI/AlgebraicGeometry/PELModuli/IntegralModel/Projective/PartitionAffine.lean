import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.Neighborhoods
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointOpenCoverFinite
import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import Mathlib.Algebra.CharZero.Infinite

/-! # Partition Affine -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionAffine

noncomputable section

/-! A finite disjoint open cover by projective varieties gives affine
neighborhoods of all finite subsets of the actual scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective

theorem projective_partition_finite_set_affine {I : Type} [Finite I]
    (V : I → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {X : Scheme.{0}}
    (f : ∀ i, (V i).carrier ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hd : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (hcover : (⋃ i, Set.range (f i)) = Set.univ)
    (F : Set X) (hF : F.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ U := by
  classical
  have hlocal (i : I) : ∃ U : (V i).carrier.Opens,
      IsAffineOpen U ∧ (f i) ⁻¹' F ⊆ U :=
    Neighborhoods.finite_set_affine_neighborhood_of_projective_embedding (K := ℂ)
      (V i).ambientDimension (V i).embedding ((f i) ⁻¹' F)
      (hF.preimage (f i).isOpenEmbedding.injective.injOn)
  choose U hU hFU using hlocal
  let W (i : I) : X.Opens := (f i) ''ᵁ U i
  have hW (i : I) : IsAffineOpen (W i) := (hU i).image_of_isOpenImmersion (f i)
  have hdis : Pairwise (fun i j => Disjoint (W i) (W j)) := by
    intro i j hij
    apply Opens.coe_disjoint.mp
    exact (hd hij).mono (Set.image_subset_range _ _) (Set.image_subset_range _ _)
  refine ⟨⨆ i, W i, IsAffineOpen.iSup_of_disjoint hW hdis, ?_⟩
  intro x hx
  have hxcover : x ∈ ⋃ i, Set.range (f i) := by rw [hcover]; trivial
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hxcover
  exact Opens.mem_iSup.mpr ⟨i, y, hFU i hx, rfl⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.PartitionAffine
