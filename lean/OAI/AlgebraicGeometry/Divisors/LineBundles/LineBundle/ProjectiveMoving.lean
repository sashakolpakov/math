import OAI.AlgebraicGeometry.Divisors.LineBundles.CommonAffineOrderApproximation
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.AffineMoving

/-! # Projective Moving -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: moving genuine line-bundle divisors away from actual principal-divisor components -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y f) (q : X ⟶ Y) [IsAffineHom q]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

include P q in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_rationalSection_avoiding_finitePoints {ι : Type*} [Finite ι]
    (x : ι → X) (hx : ∀ i, coheight (x i) = 1) (hinj : Function.Injective x)
    [∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))] :
    ∃ a : X.functionFieldˣ, ∀ i, L.rationalSectionPointDivisorWithCoefficient a (x i) = 0 := by
  obtain ⟨a, ha⟩ := CommonAffineOrderApproximation.BundleCycles.exists_affineOverProjective_prescribed_orders P q x hx hinj
    (fun i => -L.rationalSectionOrder (x i))
  refine ⟨a, fun i => ?_⟩
  change X.ord (a : X.functionField) (x i) + L.rationalSectionOrder (x i) = 0
  rw [ha i, neg_add_cancel]

include P q in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_rationalSection_avoiding_principalDivisor
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] (g : X.functionField) :
    ∃ a : X.functionFieldˣ,
      Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g).support := by
  classical
  let S := (Ord.BundleCycles.principalDivisor X g).support
  have hx : ∀ x : S, coheight x.val = 1 := by
    intro x
    by_contra hc
    have hz : Ord.BundleCycles.principalDivisor X g x.val = 0 := X.ord_eq_zero_of_coheight_neq_one hc g
    exact (Finsupp.mem_support_iff.mp x.property) hz
  obtain ⟨a, ha⟩ := L.exists_rationalSection_avoiding_finitePoints P q (fun x : S => x.val)
    hx Subtype.val_injective
  refine ⟨a, Finset.disjoint_left.mpr ?_⟩
  intro x hxA hxG
  exact (Finsupp.mem_support_iff.mp hxA) (ha ⟨x, hxG⟩)

include P q in
theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_rationalSection_class_avoiding_principalDivisor
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] (g : X.functionField)
    (h : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType h] (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension h = d + 1) :
    ∃ a : X.functionFieldˣ,
      Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g).support ∧
      Point.CycleChow.BundleCycles.pointCycleToChowQ h d (L.rationalSectionPointCycleWithCoefficient a) = L.rationalSectionChowClass h d := by
  obtain ⟨a, ha⟩ := L.exists_rationalSection_avoiding_principalDivisor P q g
  exact ⟨a, ha, L.rationalSectionChowClass_coefficient_independent h d hd a⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
