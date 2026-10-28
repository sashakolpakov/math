import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealAway

/-! # Ideal Divisor Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealDivisorSupport.BundleCycles

noncomputable section

/-! The canonical negative divisor of the actual invertible ideal
is supported on the actual closed immersion, with no extraneous components. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)

theorem cartierIdealMorphismCoordinate_unit_away (x : X) (W : X.Opens)
    (hW : W ≤ (IdealBundle.Cycles.cartierIdealLineBundle i hi).trivializingOpen x)
    (haway : ∀ z : Z, i z ∉ W) :
    IsUnit (LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate (IdealBundle.Cycles.cartierIdealLineBundle i hi)
      (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW) := by
  let L := IdealBundle.Cycles.cartierIdealLineBundle i hi
  let s := LineBundles.Scheme.IdealAway.BundleCycles.schemeIdealAwaySection i W haway
  let a := L.sectionFrame x W hW s
  let t := LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW
  have h : (1 : Γ(X, W)) = a * t :=
    (LineBundles.Scheme.IdealAway.BundleCycles.schemeIdealAwaySection_image i W haway).symm.trans
      (LineBundle.MorphismCoordinate.Cycles.lineBundleMorphismCoordinate_apply L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W hW s)
  exact ⟨⟨t, a, (mul_comm _ _).trans h.symm, h.symm⟩, rfl⟩

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem cartierIdealInverseCoefficient_divisor_off_image (x : X) (hx : x ∉ Set.range i) :
    (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
      (IdealDivisor.BundleCycles.cartierIdealInverseCoefficient i hi) x = 0 := by
  let L := IdealBundle.Cycles.cartierIdealLineBundle i hi
  let V : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let W := L.trivializingOpen x ⊓ V
  have hxW : x ∈ W := ⟨L.mem_trivializingOpen x, hx⟩
  let : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hu := cartierIdealMorphismCoordinate_unit_away i hi x W inf_le_left
    (fun z hz => hz.2 (Set.mem_range_self z))
  rw [IdealDivisor.BundleCycles.cartierIdealInverseCoefficient_divisor]
  change -X.ord (LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismFieldCoordinate L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x) x = 0
  rw [LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismFieldCoordinate_on_open L (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i) x W inf_le_left,
    Scheme.ord_of_isUnit hu hxW, neg_zero]

theorem cartierIdealInversePointCycle_support :
    (↑(IdealDivisor.BundleCycles.cartierIdealInversePointCycle i hi).support : Set X) ⊆ Set.range i := by
  intro x hx
  by_contra hn
  apply Finsupp.mem_support_iff.mp hx
  change ((IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
    (IdealDivisor.BundleCycles.cartierIdealInverseCoefficient i hi) x : ℚ) = 0
  rw [cartierIdealInverseCoefficient_divisor_off_image i hi x hn, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealDivisorSupport.BundleCycles
