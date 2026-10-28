import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.PullbackEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SectionSupportModule
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Truncation

/-! # Section Multiplicity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionMultiplicity

noncomputable section

/-! Smooth pullback and a closed section preserve every native
intersection multiplicity, for arbitrary integral cycle supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (s : Y.toOver ⟶ X.toOver) [IsClosedImmersion s.left]
  (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)] (hs : s ≫ f = 𝟙 Y.toOver)

local instance : IsLocallyNoetherian X.toOver.left := inferInstanceAs (IsLocallyNoetherian X.carrier)
local instance : IsLocallyNoetherian Y.toOver.left := inferInstanceAs (IsLocallyNoetherian Y.carrier)

include hs in
theorem euler (B D : IrreducibleCloseds Y.carrier) (x : X.carrier)
    (hxB : f.left x ∈ (B : Set Y.carrier)) (hxD : x ∈ (ProperCycleLinearity.imageSupport s D : Set X.carrier)) (d : ℕ) :
    (∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (CycleClass.Thom.IntersectionGeometry.localTorLength X.carrier (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f.left B) (ProperCycleLinearity.imageSupport s D) x
        (PullbackModule.mem f.left B x hxB) hxD i).toNat) =
    ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i *
      (CycleClass.Thom.IntersectionGeometry.localTorLength Y.carrier B D (f.left x) hxB (SectionSupportModule.mem s f hs D x hxD) i).toNat := by
  have hr : x ∈ Set.range s.left := by
    rw [ProperCycleLinearity.imageSupport_eq_image] at hxD
    exact ⟨hxD.choose, hxD.choose_spec.2⟩
  have he := PullbackEuler.euler f.left (ProperCycleLinearity.imageSupport s D) B x hxD hxB d
  rw [SectionSupportModule.residueDegree s f hs x hr, Nat.cast_one, mul_one] at he
  exact he.symm.trans (PullbackEuler.congr (Y.carrier.presheaf.stalk (f.left x))
    (Iso.refl (CycleClass.Thom.IntersectionGeometry.localSupportModule Y.carrier B (f.left x) hxB))
    (SectionSupportModule.equiv s f hs D x hxD).toModuleIso.symm d)

include hs in
theorem multiplicity (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (B D C : IrreducibleCloseds Y.carrier) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport f.left B) (ProperCycleLinearity.imageSupport s D) (ProperCycleLinearity.imageSupport s C) =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity Y B D C := by
  have hx : CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport s C) = s.left (CycleClass.Thom.IntersectionGeometry.supportPoint C) :=
    irreducibleSetEquivPoints.apply_symm_apply _
  have hfx : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport s C)) = CycleClass.Thom.IntersectionGeometry.supportPoint C :=
    (congrArg f.left hx).trans (SmoothSectionGeometry.point s f hs _)
  have hm : CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport s C) ∈
      (Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport (show X.carrier ⟶ Y.carrier from f.left) B : Set X.carrier) ∩
        (ProperCycleLinearity.imageSupport s D : Set X.carrier) ↔
      CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set Y.carrier) ∩ D := by
    rw [Divisors.LineBundles.Integral.PulledSupport.BundleCycles.integralPulledSupport_coe]
    change (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport s C)) ∈ (B : Set Y.carrier) ∧
      CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport s C) ∈ (ProperCycleLinearity.imageSupport s D : Set X.carrier)) ↔ _
    rw [hfx, ProperCycleLinearity.imageSupport_eq_image, hx]
    constructor
    · rintro ⟨hB, y, hy, he⟩
      exact ⟨hB, s.left.isClosedEmbedding.injective he ▸ hy⟩
    · rintro ⟨hB, hD⟩
      exact ⟨hB, _, hD, rfl⟩
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set Y.carrier) ∩ D
  · have hX := hm.mpr h
    have hB : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport s C)) ∈ (B : Set Y.carrier) := hfx.symm ▸ h.1
    rw [Truncation.intersectionMultiplicity_eq_relative_sum X m _ _ _ hX.1 hX.2,
      Truncation.intersectionMultiplicity_eq_relative_sum Y n _ _ _ h.1 h.2]
    rw [← Truncation.local_euler_sum_stable X m _ _ _ hX.1 hX.2 (m + n) (by omega),
      euler s f hs B D _ hB hX.2 (m + n)]
    have he := Truncation.local_euler_sum_stable Y n B D
      (CycleClass.Thom.IntersectionGeometry.supportPoint C) h.1 h.2 (m + n) (by omega)
    trans ∑ i ∈ Finset.range ((m + n) + 1), (-1 : ℚ) ^ i *
      (CycleClass.Thom.IntersectionGeometry.localTorLength Y.carrier B D (CycleClass.Thom.IntersectionGeometry.supportPoint C) h.1 h.2 i).toNat
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact congrArg (fun l : ℕ∞ => (l.toNat : ℚ))
        (Open.SupportTor.localTorLength_congr_point Y.carrier B D hfx hB
          (SectionSupportModule.mem s f hs D _ hX.2) h.1 h.2 i)
    · exact he
  · rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right (fun hX => h (hm.mp hX)),
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right h]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionMultiplicity
