import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryEtaleTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleMapsFromPoints

/-! # Compact Ordinary Point Type -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactOrdinaryPointType.Construction

noncomputable section

/-! Rational points distinguish the two pure compact ordinary types.
A point-bijective native block map therefore preserves that type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (k : Type) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]

local notation "T₀" => Over.mk (𝟙 (Spec (CommRingCat.of k)))

theorem ordinaryPureMultiplicative_point_eq_one {G : Grp (Over (Spec (.of k)))} {d : ℕ}
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 d 0) (x : T₀ ⟶ G.X) : x = 1 := by
  let i := (OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom
  have : IsIso i := CompactKernels.Construction.ordinaryPureMultiplicative_inclusion_isIso k q 1 e
  have : Smooth (T₀).hom := inferInstanceAs (Smooth (𝟙 (Spec (.of k))))
  have : IsReduced (T₀).left := ArithmeticGeometry.OrdinaryLocus.Openness.SmoothReduced.Construction.isReduced_smooth_over_field (T₀).hom
  have hx : x ≫ inv i = 1 := ReducedHeightOneMaps.Construction.map_from_reduced_of_trivial_frobenius q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) _
    (Multiplicative.Construction.ordinaryMultiplicative_relativeFrobenius q k d)
  have hcancel : (x ≫ inv i) ≫ i = x :=
    (Category.assoc x (inv i) i).trans
      ((congrArg (fun z => x ≫ z) (IsIso.inv_hom_id i)).trans (Category.comp_id x))
  exact hcancel.symm.trans ((congrArg (fun z => z ≫ i) hx).trans (MonObj.one_comp i))

omit [CharP k q] in
theorem ordinaryPureEtale_point_ne_one {G : Grp (Over (Spec (.of k)))}
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 0 3) : ∃ x : T₀ ⟶ G.X, x ≠ 1 := by
  have : Fact (1 < q ^ 1) := ⟨by simpa only [pow_one] using (Fact.out : q.Prime).one_lt⟩
  let ep := EtaleLabelTransport.Construction.fieldEtalePointsEquiv k (OrdinaryBlocks.Construction.OrdinaryBlockLabels q 1 3)
  obtain ⟨c, hc⟩ := exists_ne (1 : OrdinaryBlocks.Construction.OrdinaryBlockLabels q 1 3)
  let z := ep.symm c
  have hz : z ≠ 1 := by
    intro h
    exact hc ((ep.apply_symm_apply c).symm.trans ((congrArg ep h).trans ep.map_one))
  let i := (OrdinaryEtaleTransport.Construction.ordinaryEtaleInclusion q k e).hom.hom
  have : Mono i := OrdinaryEtaleTransport.Construction.ordinaryEtaleInclusion_mono_underlying q k e
  refine ⟨z ≫ i, fun h => hz ?_⟩
  exact (cancel_mono i).mp (h.trans (MonObj.one_comp i).symm)

theorem compactOrdinaryType_eq_of_points_bijective
    {G G' : Grp (Over (Spec (.of k)))} (b b' : Bool)
    (e : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 (if b then 3 else 0) (if b then 0 else 3))
    (e' : OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G' q 1 (if b' then 3 else 0) (if b' then 0 else 3))
    (a : G ⟶ G') (ha : Function.Bijective ((yonedaGrp.map a).app (.op T₀))) : b = b' := by
  cases b <;> cases b'
  · rfl
  · obtain ⟨x, hx⟩ := ordinaryPureEtale_point_ne_one k q e
    have hax : x ≫ a.hom.hom = 1 := ordinaryPureMultiplicative_point_eq_one k q e' _
    exact False.elim (hx (ha.1 (hax.trans (MonObj.one_comp a.hom.hom).symm)))
  · obtain ⟨y, hy⟩ := ordinaryPureEtale_point_ne_one k q e'
    obtain ⟨x, hx⟩ := ha.2 y
    have hx1 : x = 1 := ordinaryPureMultiplicative_point_eq_one k q e x
    exact False.elim (hy (hx.symm.trans
      ((congrArg (fun z => z ≫ a.hom.hom) hx1).trans (MonObj.one_comp a.hom.hom))))
  · rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactOrdinaryPointType.Construction
