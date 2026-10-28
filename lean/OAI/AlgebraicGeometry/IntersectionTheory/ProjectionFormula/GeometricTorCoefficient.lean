import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedTorEuler

/-! # Geometric Tor Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricTorCoefficient

noncomputable section

/-! The localized algebraic Tor Euler coefficient is the native
geometric coefficient at the corresponding support point. On a
projective presentation this is ThomClass's intersection multiplicity. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

def coefficient (Z : Scheme) (A B : IrreducibleCloseds Z)
    (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z)) (d : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (d + 1), (-1 : ℚ) ^ i * (CycleClass.Thom.IntersectionGeometry.localTorLength Z A B x hxA hxB i).toNat

theorem localization (Z : Scheme) (A B : IrreducibleCloseds Z)
    (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))
    (p : PrimeSpectrum (Z.presheaf.stalk x))
    (hpA : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))
    (hpB : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) (d : ℕ) :
    coefficient Z A B (Z.fromSpecStalk x p)
      (Local.SupportSpectrum.image_mem_support Z A x hxA p hpA)
      (Local.SupportSpectrum.image_mem_support Z B x hxB p hpB) d =
    Tor.Euler.euler (Localization.AtPrime p.asIdeal)
      ((Flat.Extension.baseChange (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))
      ((Flat.Extension.baseChange (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) d := by
  rw [LocalizedTorEuler.euler]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun n : ℕ∞ => (-1 : ℚ) ^ i * (n.toNat : ℚ))
    (GeometricSupportLocalization.Tor.length Z A B x hxA hxB p hpA hpB i)

theorem intersectionMultiplicity (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier)) (hxB : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier)) :
    coefficient X.carrier A B (CycleClass.Thom.IntersectionGeometry.supportPoint C) hxA hxB X.ambientDimension =
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C := by
  rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨hxA, hxB⟩]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricTorCoefficient
