import Mathlib.Algebra.Homology.QuasiIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.ComplexExtension
import Mathlib.Algebra.Homology.Embedding.Restriction

/-! # Supported Complex Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedComplexRestriction

noncomputable section

/-! Restricting a complex to any embedded shape containing all its nonzero terms and extending by zero recovers the original complex. Exactness consequently agrees at every retained vertex, including both endpoints of a finite interval. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w
variable {V : Type u} [Category.{v} V] [Abelian V]
  {ι ι' : Type w} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') [e.IsRelIff] (K : HomologicalComplex V c') [K.IsStrictlySupported e]

def supportedRestrictionExtendXIso (j : ι') :
    ((K.restriction e).extend e).X j ≅ K.X j := by
  classical
  exact if h : ∃ i, e.f i = j then
      (K.restriction e).extendXIso e h.choose_spec ≪≫ K.restrictionXIso e h.choose_spec
    else
      IsZero.iso ((K.restriction e).isZero_extend_X e j (by simpa using h))
        (K.isZero_X_of_isStrictlySupported e j (by simpa using h))

theorem supportedRestrictionExtendXIso_in {i : ι} {j : ι'} (h : e.f i = j) :
    supportedRestrictionExtendXIso e K j =
      (K.restriction e).extendXIso e h ≪≫ K.restrictionXIso e h := by
  classical
  have hex : ∃ k, e.f k = j := ⟨i, h⟩
  simp only [supportedRestrictionExtendXIso, dite_eq_left hex]
  have he : hex.choose = i := e.injective_f (hex.choose_spec.trans h.symm)
  subst i
  rfl

def supportedRestrictionExtendIso : (K.restriction e).extend e ≅ K := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (supportedRestrictionExtendXIso e K) ?_
  intro i' j' _
  by_cases hi : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi
    by_cases hj : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj
      rw [supportedRestrictionExtendXIso_in e K hi, supportedRestrictionExtendXIso_in e K hj,
        (K.restriction e).extend_d_eq e hi hj, K.restriction_d_eq e hi hj]
      simp [Category.assoc]
    · exact (K.isZero_X_of_isStrictlySupported e j' (by simpa using hj)).eq_of_tgt _ _
  · exact ((K.restriction e).isZero_extend_X e i' (by simpa using hi)).eq_of_src _ _

theorem strictlySupported_restriction_exactAt_iff (j : ι) :
    (K.restriction e).ExactAt j ↔ K.ExactAt (e.f j) :=
  ((K.restriction e).extend_exactAt_iff e rfl).symm.trans
    (exactAt_iff_of_quasiIsoAt (supportedRestrictionExtendIso e K).hom (e.f j))

theorem strictlySupported_restriction_acyclic (hK : K.Acyclic) : (K.restriction e).Acyclic :=
  fun j => (strictlySupported_restriction_exactAt_iff e K j).mpr (hK (e.f j))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SupportedComplexRestriction
