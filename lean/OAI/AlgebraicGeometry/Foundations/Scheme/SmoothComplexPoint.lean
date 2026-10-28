import OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothJacobian
import OAI.AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Smooth Complex Point -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SmoothComplexPoint.Algebraic

noncomputable section

/-!
# Standard smooth neighborhoods of field-valued points

A smooth algebra has a standard smooth principal neighborhood of each actual
field-valued point. Its character extends to that localization, where the
polynomial presentation has full Jacobian row rank. In particular these
statements apply to complex algebras and complex points. No analytic topology
or implicit function theorem is assumed here.
-/

universe u v

variable {K : Type u} {S : Type v}
variable [Field K] [CommRing S] [Algebra K S]

/-- A smooth algebra has a standard smooth principal neighborhood of every
field-valued point. Nonvanishing is proved at the actual character. -/
theorem smooth_point_exists_standardSmooth_away [Algebra.Smooth K S]
    (x : S →ₐ[K] K) :
    ∃ g : S, x g ≠ 0 ∧ Algebra.IsStandardSmooth K (Localization.Away g) := by
  let : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  obtain ⟨g, hg, hstd⟩ :=
    Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K (RingHom.ker x)
  refine ⟨g, ?_, hstd⟩
  simpa only [RingHom.mem_ker] using hg

/-- On such a neighborhood the extended point admits a genuine finite
submersive presentation with full evaluated Jacobian row rank. -/
theorem smooth_point_exists_submersive_presentation [Algebra.Smooth K S]
    (x : S →ₐ[K] K) :
    ∃ (g : S) (hg : x g ≠ 0) (n m : ℕ)
      (P : Algebra.SubmersivePresentation K (Localization.Away g) (Fin n) (Fin m)),
      (StandardSmoothJacobian.Algebraic.pointJacobian P.toPresentation (LocalizationComplexPoints.Algebraic.localizePoint x g hg)).rank = m := by
  obtain ⟨g, hg, hstd⟩ := smooth_point_exists_standardSmooth_away x
  let : Algebra.IsStandardSmooth K (Localization.Away g) := hstd
  obtain ⟨n, m, P, hP⟩ := StandardSmoothJacobian.Algebraic.exists_pointJacobian_full_row_rank (LocalizationComplexPoints.Algebraic.localizePoint x g hg)
  exact ⟨g, hg, n, m, P, hP⟩

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SmoothComplexPoint.Algebraic
