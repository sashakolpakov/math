import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Support
import Mathlib.RingTheory.Ideal.Height

/-! # Prime Quotient Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeQuotientLocalization

noncomputable section

/-! Prime quotients vanish after localization away from their support;
height at least two makes this hold at every height-one prime. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R]

theorem annihilated (p : Ideal R) (r : R) (hr : r ∈ p) (x : R ⧸ p) : r • x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk p (r * a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (p.mul_mem_right a hr)

theorem localized_isZero (p q : Ideal R) [q.IsPrime] (h : ¬ p ≤ q) :
    IsZero ((Flat.Extension.baseChange R (Localization.AtPrime q)).obj
      (ModuleCat.of R (R ⧸ p))) := by
  obtain ⟨r, hrp, hrq⟩ := SetLike.not_le_iff_exists.mp h
  let : Subsingleton (LocalizedModule q.primeCompl (R ⧸ p)) :=
    LocalizedModule.subsingleton_iff.mpr (fun x => ⟨r, hrq, annihilated R p r hrp x⟩)
  let : Subsingleton (Localization.AtPrime q ⊗[R] (R ⧸ p)) :=
    (LocalizedModule.equivTensorProduct q.primeCompl (R ⧸ p)).symm.injective.subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (inferInstanceAs (Subsingleton (Localization.AtPrime q ⊗[R] (R ⧸ p))))

theorem height_one_isZero (p : Ideal R) (hp : 1 < p.height)
    (q : Ideal R) [q.IsPrime] (hq : q.height = 1) :
    IsZero ((Flat.Extension.baseChange R (Localization.AtPrime q)).obj
      (ModuleCat.of R (R ⧸ p))) := by
  apply localized_isZero R p q
  intro hle
  exact (not_le_of_gt hp) ((Ideal.height_mono hle).trans hq.le)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeQuotientLocalization
