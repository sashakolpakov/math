import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulEulerDifference
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneMixedKoszulSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerEulerDifferenceOrbit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerMixedPowerDifferences

/-! # Hyperplane Mixed Euler Coefficient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneMixedEulerCoefficient

noncomputable section

/-! One hyperplane and g sections pulled back to the d-th power have
mixed Euler coefficient c (g+1)! d^g when the actual integer Euler
orbit of the line bundle is the degree-(g+1) monomial with coefficient c. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem mixedEulerDifference_eq_power_of_constant_class {X : Scheme.{u}}
    (bs : List (LineBundleKoszulComplex.LineBundleSection X)) (a : Line.Bundles.LineBundle.IsoClass X)
    (h : ∀ b ∈ bs, Line.Bundles.LineBundle.classOf b.1 = a) :
    MixedKoszulEulerDifference.mixedLineBundleEulerDifference X bs = (LineBundle.EulerShifts.lineBundleEulerShift X a - 1) ^ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [MixedKoszulEulerDifference.mixedLineBundleEulerDifference, h b (by simp),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb)), List.length_cons, pow_succ']

theorem hyperplanePullbackSections_eulerDifference {X : Scheme.{u}}
    (L : Line.Bundles.LineBundle X) (a : Line.Bundles.structureModule X ⟶ L.sheaf) (m : X ⟶ X)
    (ts : List (Line.Bundles.structureModule X ⟶ L.sheaf)) :
    MixedKoszulEulerDifference.mixedLineBundleEulerDifference X (HyperplaneMixedKoszulSupport.hyperplanePullbackSections L a m ts) =
      (LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L) - 1) *
        (LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf (L.pullback m)) - 1) ^ ts.length := by
  rw [HyperplaneMixedKoszulSupport.hyperplanePullbackSections, MixedKoszulEulerDifference.mixedLineBundleEulerDifference,
    mixedEulerDifference_eq_power_of_constant_class _ (Line.Bundles.LineBundle.classOf (L.pullback m))]
  · rw [List.length_map]
  · intro b hb
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hb
    rfl

theorem hyperplanePullbackSections_monomial_eulerDifference {X : Scheme.{u}}
    (L : Line.Bundles.LineBundle X) (a : Line.Bundles.structureModule X ⟶ L.sheaf) (m : X ⟶ X)
    (ts : List (Line.Bundles.structureModule X ⟶ L.sheaf)) (g : ℕ) (hlen : ts.length = g)
    (f : Line.Bundles.LineBundle.IsoClass X → ℤ) (c d : ℤ) (hd : d ≠ 0)
    (hclass : Line.Bundles.LineBundle.classOf (L.pullback m) = Line.Bundles.LineBundle.classOf L ^ d)
    (hf : ∀ z : ℤ, f (Line.Bundles.LineBundle.classOf L ^ z) = c * z ^ (g + 1)) :
    MixedKoszulEulerDifference.mixedLineBundleEulerDifference X (HyperplaneMixedKoszulSupport.hyperplanePullbackSections L a m ts) f 1 =
      c * ((g + 1).factorial : ℤ) * d ^ g := by
  rw [hyperplanePullbackSections_eulerDifference, hlen, hclass,
    IntegerEulerDifferenceOrbit.lineBundleEulerDifference_mixed_orbit]
  have horbit : (fun z : ℤ => f (Line.Bundles.LineBundle.classOf L ^ z)) =
      (fun z : ℤ => c * z ^ (g + 1)) := funext hf
  rw [horbit]
  exact IntegerMixedPowerDifferences.integer_mixedMonomial_finiteDifference g c d 0 hd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HyperplaneMixedEulerCoefficient
