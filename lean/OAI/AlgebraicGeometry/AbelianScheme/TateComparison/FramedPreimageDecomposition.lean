import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedBlockLattices

/-! # Framed Preimage Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! An actual isogeny's full Tate preimage is the product of its
projected block lattices in any compatible source frame. Thus equality
of all block lattices implies equality of the full intrinsic preimages. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k] {m n : ℕ}
  {P Q Q' : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (frame : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
  (hf : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (δ : Fin (3 * s) → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

include hg hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.framedTateLattice_single_mem (v : Fin s × Bool)
    (z : Fin 3 → ℚ_[q]) (hz : z ∈ Rational.framedTateLattice frame e.isogeny.hom v) :
    (Pi.single v z : Rational.SplitTateSpace s q) ∈
      (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom).map
        (frame.toLinearMap.restrictScalars ℤ_[q]) := by
  classical
  rw [← D.framedTargetBlockMap_range hg e frame hf δ hδ hq v] at hz
  obtain ⟨a, rfl⟩ := hz
  refine ⟨D.targetBlockToTateSpace hg (𝟙 (Spec (.of k))) e v a,
    (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny a.val).property, ?_⟩
  funext w i
  change frame (D.targetBlockToTateSpace hg (𝟙 (Spec (.of k))) e v a) w i =
    (Pi.single v (D.framedTargetBlockMap hg e frame v a) : Rational.SplitTateSpace s q) w i
  by_cases hw : w = v
  · subst w
    simp only [Pi.single_eq_same, Data.SphericalPELAlbaneseData.framedTargetBlockMap_apply]
  · rw [D.preimageFrameCoordinate_off_block hg e frame hf δ hδ hq (Ne.symm hw) a i]
    simp only [Pi.single_eq_of_ne hw, Pi.zero_apply]

include hg hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.framedTatePreimage_eq_pi :
    (Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom).map
        (frame.toLinearMap.restrictScalars ℤ_[q]) =
      Submodule.pi Set.univ (Rational.framedTateLattice frame e.isogeny.hom) := by
  classical
  apply le_antisymm
  · intro z hz v _
    exact ⟨z, hz, rfl⟩
  · intro z hz
    rw [← Finset.univ_sum_single z]
    exact Submodule.sum_mem _ fun v _ =>
      D.framedTateLattice_single_mem hg e frame hf δ hδ hq v (z v) (hz v (Set.mem_univ v))

include hg hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.preimage_eq_of_framedTateLattice_eq (f : PELIsogenies.PELIsogeny P Q' (q ^ n))
    (h : ∀ v, Rational.framedTateLattice frame e.isogeny.hom v =
      Rational.framedTateLattice frame f.isogeny.hom v) :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom := by
  apply Submodule.map_injective_of_injective
    (f := frame.toLinearMap.restrictScalars ℤ_[q]) frame.injective
  rw [D.framedTatePreimage_eq_pi hg e frame hf δ hδ hq,
    D.framedTatePreimage_eq_pi hg f frame hf δ hδ hq]
  rw [funext h]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
