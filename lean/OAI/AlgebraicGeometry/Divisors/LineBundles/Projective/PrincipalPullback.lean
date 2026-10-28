import OAI.AlgebraicGeometry.Divisors.LineBundles.IdealComapAffineChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.CoordinateSectionMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalSectionKernel
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapCongr

/-! # Principal Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalPullback.BundleCycles

noncomputable section

/-! A commuting square of actual homogeneous principal quotients
is Cartesian when the lower equation is the image of the upper equation. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem projectivePrincipal_isPullback
    {A B C D σ τ υ ω : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    [SetLike υ C] [AddSubgroupClass υ C] [SetLike ω D] [AddSubgroupClass ω D]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → υ} {𝒟 : ℕ → ω}
    [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒟]
    (f : 𝒜 →+*ᵍ ℬ) (i : 𝒜 →+*ᵍ 𝒞) (j : ℬ →+*ᵍ 𝒟) (g : 𝒞 →+*ᵍ 𝒟)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hi : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map i)
    (hj : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant ℬ).map j)
    (hg : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒞).map g)
    (hSurjI : Function.Surjective i) (hSurjJ : Function.Surjective j)
    (h : j.comp f = g.comp i) (t : A) (ht : t ∈ 𝒜 1)
    (hki : RingHom.ker i.toRingHom = Ideal.span {t})
    (hkj : RingHom.ker j.toRingHom = Ideal.span {f t})
    (hcover : ∀ x : Proj 𝒜, ∃ v : A, v ∈ 𝒜 1 ∧ x ∈ Proj.basicOpen 𝒜 v) :
    IsPullback (Proj.map j hj) (Proj.map g hg) (Proj.map f hf) (Proj.map i hi) := by
  let : IsClosedImmersion (Proj.map i hi) := ClosedImmersion.BundleCycles.projectiveMap_isClosedImmersion i hi hSurjI
  let : IsClosedImmersion (Proj.map j hj) := ClosedImmersion.BundleCycles.projectiveMap_isClosedImmersion j hj hSurjJ
  apply isPullback_of_isClosedImmersion
  · exact (Proj.map_comp f j hf hj).symm.trans
      ((MapCongr.BundleCycles.projectiveMap_congr h _ _).trans (Proj.map_comp i g hi hg))
  · let V (v : {v : A // v ∈ 𝒜 1}) : (Proj ℬ).affineOpens :=
      ⟨Proj.basicOpen ℬ (f v.val), Proj.isAffineOpen_basicOpen ℬ _ (f.map_mem v.property) (by decide)⟩
    have hV : ⨆ v, (V v).1 = ⊤ := by
      apply le_antisymm le_top
      intro x _
      obtain ⟨v, hv, hxv⟩ := hcover (Proj.map f hf x)
      exact Opens.mem_iSup.mpr ⟨⟨v, hv⟩, hxv⟩
    apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hV
    intro v
    let U : (Proj 𝒜).affineOpens :=
      ⟨Proj.basicOpen 𝒜 v.val, Proj.isAffineOpen_basicOpen 𝒜 v.val v.property (by decide)⟩
    have hLeft := IdealComapAffineChart.BundleCycles.idealComap_affineChart (Proj.map i hi) (Proj.map f hf) U (V v) le_rfl
    have hBase := PrincipalSectionKernel.BundleCycles.projectivePrincipalSection_kernel i hi v.val t v.property ht hki
    have hTarget := PrincipalSectionKernel.BundleCycles.projectivePrincipalSection_kernel j hj (f v.val) (f t) (f.map_mem v.property) (f.map_mem ht) hkj
    have hMap : (Proj.map f hf).appLE U.1 (V v).1 le_rfl
        (CoordinateSectionMap.BundleCycles.projectiveCoordinateSection 𝒜 v.val t v.property ht) =
      CoordinateSectionMap.BundleCycles.projectiveCoordinateSection ℬ (f v.val) (f t) (f.map_mem v.property) (f.map_mem ht) :=
      CoordinateSectionMap.BundleCycles.projectiveCoordinateSection_map f hf v.val t v.property ht
    refine hLeft.trans (Eq.trans ?_ (hTarget.symm.trans (Scheme.Hom.ker_apply (Proj.map j hj) (V v)).symm))
    rw [hBase, Ideal.map_span, Set.image_singleton, hMap]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.PrincipalPullback.BundleCycles
