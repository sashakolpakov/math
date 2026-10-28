import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Disjoint Open Cover Finite -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointOpenCoverFinite

noncomputable section

/-! A disjoint open cover of a compact scheme by nonempty schemes has
finitely many components. Its actual coproduct map is an isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {I : Type} {X : Scheme.{0}} (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (f i)]

theorem disjoint_open_cover_finite [CompactSpace X] [∀ i, Nonempty (Y i)]
    (hd : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (hcover : (⋃ i, Set.range (f i)) = Set.univ) : Finite I := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun i => Set.range (f i))
    (fun i => (f i).isOpenEmbedding.isOpen_range) (by rw [hcover])
  have hall (i : I) : i ∈ t := by
    let y : Y i := Classical.choice inferInstance
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ (f i y)))
    obtain ⟨hjt, hy⟩ := Set.mem_iUnion.mp hj
    by_cases hij : i = j
    · exact hij.symm ▸ hjt
    · exact False.elim (Set.disjoint_left.mp (hd hij) (Set.mem_range_self y) hy)
  exact Set.finite_univ_iff.mp (t.finite_toSet.subset (fun i _ => hall i))

theorem disjoint_open_cover_sigma_isIso
    (hd : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))))
    (hcover : (⋃ i, Set.range (f i)) = Set.univ) : IsIso (Sigma.desc f) := by
  have : IsOpenImmersion (Sigma.desc f) := isOpenImmersion_sigmaDesc Y f hd
  have : Surjective (Sigma.desc f) := Surjective.sigmaDesc_of_union_range_eq_univ hcover
  exact (isIso_iff_isOpenImmersion_and_surjective (Sigma.desc f)).mpr ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.DisjointOpenCoverFinite
