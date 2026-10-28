import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealSubopenEquation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealDivisorSupport

/-! # Cartier Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierDivisor.BundleCycles

noncomputable section

/-! The actual ideal of an integral effective Cartier divisor
represents minus its reduced generic-point cycle, with multiplicity one. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

theorem specializes_eq_of_coheight_one {X : Scheme.{0}} {x y : X}
    (h : x ⤳ y) (hx : coheight x = 1) (hy : coheight y = 1) : x = y := by
  by_contra hne
  have hlt : y < x := lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr h,
    fun hxy => hne (h.antisymm (Scheme.le_iff_specializes.mp hxy)).eq⟩
  have hc := coheight_strictAnti hlt (show coheight x < ⊤ by rw [hx]; decide)
  rw [hx, hy] at hc
  exact (lt_irrefl (1 : ℕ∞)) hc

variable {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] [AlgebraicGeometry.IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (hi : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)

theorem integralCartierIdeal_generic_multiplicity :
    (Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
      (Cartier.IdealDivisor.BundleCycles.cartierIdealInverseCoefficient i hi) (i (genericPoint Z)) = -1 := by
  let L := Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi
  let x := i (genericPoint Z)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (L.mem_trivializingOpen x)
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  let t := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hWU
  have hk : Ideal.span {X.presheaf.germ W x hxW t} = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (Closed.ImmersionStalkKernel.BundleCycles.closedImmersion_principal_stalk_kernel i W hW (genericPoint Z) hxW t
      (Cartier.IdealSubopenEquation.BundleCycles.cartierIdealSubopenEquation_kernel i hi x W hWU)).symm.trans
        (IsLocalRing.ker_eq_maximalIdeal (i.stalkMap (genericPoint Z)).hom (i.stalkMap_surjective _))
  rw [Cartier.IdealDivisor.BundleCycles.cartierIdealInverseCoefficient_divisor]
  change -X.ord (LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismFieldCoordinate L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x) x = -1
  rw [LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismFieldCoordinate_on_open L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hWU,
    Open.RegularOrder.BundleCycles.openRegular_order_length W t (Cartier.IdealSubopenEquation.BundleCycles.cartierIdealSubopenEquation_ne_zero i hi x W hWU) x hxW
      (CartierGenericPoint.BundleCycles.integralCartier_genericPoint_coheight i hi), hk, FlatOrderEq.BundleCycles.FlatOrder.residue_quotient_length]
  rfl

theorem integralCartierIdeal_divisor :
    (Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
      (Cartier.IdealDivisor.BundleCycles.cartierIdealInverseCoefficient i hi) = Finsupp.single (i (genericPoint Z)) (-1) := by
  ext x
  by_cases hx : x = i (genericPoint Z)
  · subst x
    rw [Finsupp.single_eq_same, integralCartierIdeal_generic_multiplicity]
  · rw [Finsupp.single_eq_of_ne hx]
    by_contra hn
    have hc : coheight x = 1 := by
      by_contra hc
      rw [Cartier.IdealDivisor.BundleCycles.cartierIdealInverseCoefficient_divisor, Scheme.ord_eq_zero_of_coheight_neq_one hc, neg_zero] at hn
      exact hn rfl
    have hr : x ∈ Set.range i := by
      by_contra hr
      exact hn (Cartier.IdealDivisorSupport.BundleCycles.cartierIdealInverseCoefficient_divisor_off_image i hi x hr)
    obtain ⟨z, rfl⟩ := hr
    exact hx (specializes_eq_of_coheight_one ((genericPoint_specializes z).map i.continuous)
      (CartierGenericPoint.BundleCycles.integralCartier_genericPoint_coheight i hi) hc).symm

theorem integralCartierIdeal_pointCycle :
    Cartier.IdealDivisor.BundleCycles.cartierIdealInversePointCycle i hi = Finsupp.single (i (genericPoint Z)) (-1) := by
  change Finsupp.mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero
    ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient _) = _
  rw [integralCartierIdeal_divisor, Finsupp.mapRange_single]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierDivisor.BundleCycles
