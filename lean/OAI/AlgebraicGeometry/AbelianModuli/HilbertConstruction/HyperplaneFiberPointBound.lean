import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.EulerPointBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneMixedEulerCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.FieldDimensionBound

/-! # Hyperplane Fiber Point Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneFiberPointBound

noncomputable section

/-! The intersection of a hyperplane with a finite configuration in
one fiber of a locally quasi-finite endomorphism has cardinality at
most c (g+1)! d^g. The finite cuts, sheaf exactness, multiplicity-aware
Euler calculation, and point count are all supplied by the geometry. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

theorem hyperplane_fiber_configuration_card_le
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IrreducibleSpace X]
    (p : X ⟶ Spec (.of K)) [IsProper p] (g : ℕ) [SmoothOfRelativeDimension (g + 1) p]
    (L : Line.Bundles.LineBundle X) {n : ℕ} (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hcover : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) (hgen : Section.ProjectivePresentation.SectionRatiosGenerate p s)
    (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (m : X ⟶ X) [LocallyQuasiFinite m] (c d : ℤ) (hd : d ≠ 0)
    (hclass : Line.Bundles.LineBundle.classOf (L.pullback m) = Line.Bundles.LineBundle.classOf L ^ d)
    (heuler : ∀ w : ℤ, LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf L ^ w) = c * w ^ (g + 1))
    (a : Line.Bundles.structureModule X ⟶ L.sheaf) (ha_nonzero : ∃ x, x ∈ Ample.LineBundles.sectionNonvanishing a)
    {ι : Type v} [Finite ι] (x : ι → X) (hx : Function.Injective x)
    (hxa : ∀ i, x i ∉ Ample.LineBundles.sectionNonvanishing a)
    (hxm : ∀ i, m (x i) = z (IsLocalRing.closedPoint K)) :
    (Nat.card ι : ℤ) ≤ c * ((g + 1).factorial : ℤ) * d ^ g := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨ts, hts, hzts, hfinite⟩ := HyperplaneMixedKoszulSupport.exists_hyperplane_mixedKoszul_finite_support
    p L s hcover ha hgen z hz m g (Smooth.FieldDimensionBound.smoothField_topologicalKrullDim_le p (g + 1)) a ha_nonzero
  let bs := HyperplaneMixedKoszulSupport.hyperplanePullbackSections L a m ts
  have hlen : bs.length = g + 1 := by rw [HyperplaneMixedKoszulSupport.hyperplanePullbackSections_length, hts]
  have hzero : ∀ i, x i ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs := by
    intro i
    rw [HyperplaneMixedKoszulSupport.hyperplanePullbackSections_zeroSet]
    exact ⟨hxa i, fun t ht => by rw [hxm i]; exact hzts t ht⟩
  have h := FiniteIntersection.EulerPointBound.finiteIntersection_configuration_card_le_mixedEulerDifference p (g + 1) (by omega)
    (Line.Bundles.LineBundle.trivial X) bs hlen hfinite x hx hzero
  rw [Line.Bundles.LineBundle.classOf_trivial] at h
  exact h.trans_eq (HyperplaneMixedEulerCoefficient.hyperplanePullbackSections_monomial_eulerDifference L a m ts g hts
    (LineBundle.EulerShifts.lineBundleClassEuler p) c d hd hclass heuler)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneFiberPointBound
