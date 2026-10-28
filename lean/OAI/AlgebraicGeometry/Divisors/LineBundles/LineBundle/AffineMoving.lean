import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.AffineOrderApproximation
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DivisorChow

/-! # Affine Moving -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: moving the actual rational-section divisor off finitely many normal affine points -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_rationalSection_avoiding_affinePoints {ι : Type*} [Finite ι]
    (x : ι → Spec (CommRingCat.of R)) (hx : ∀ i, coheight (j (x i)) = 1)
    (hinj : Function.Injective x) [∀ i, IsIntegrallyClosed (X.presheaf.stalk (j (x i)))] :
    ∃ a : X.functionFieldˣ, ∀ i, L.rationalSectionPointDivisorWithCoefficient a (j (x i)) = 0 := by
  obtain ⟨a, ha⟩ := Open.AffineOrderApproximation.BundleCycles.exists_openAffine_prescribed_orders j x hx hinj
    (fun i => -L.rationalSectionOrder (j (x i)))
  refine ⟨a, fun i => ?_⟩
  change X.ord (a : X.functionField) (j (x i)) + L.rationalSectionOrder (j (x i)) = 0
  rw [ha i, neg_add_cancel]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_rationalSection_representative_avoiding_affinePoints {ι : Type*} [Finite ι]
    (x : ι → Spec (CommRingCat.of R)) (hx : ∀ i, coheight (j (x i)) = 1)
    (hinj : Function.Injective x) [∀ i, IsIntegrallyClosed (X.presheaf.stalk (j (x i)))]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    ∃ a : X.functionFieldˣ,
      Disjoint ((L.rationalSectionPointDivisorWithCoefficient a).support : Set X) (Set.range (fun i => j (x i))) ∧
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (L.rationalSectionPointCycleWithCoefficient a) = L.rationalSectionChowClass f d := by
  obtain ⟨a, ha⟩ := L.exists_rationalSection_avoiding_affinePoints j x hx hinj
  refine ⟨a, ?_, L.rationalSectionChowClass_coefficient_independent f d hd a⟩
  apply Set.disjoint_left.mpr
  rintro y hy ⟨i, rfl⟩
  exact (Finsupp.mem_support_iff.mp hy) (ha i)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
