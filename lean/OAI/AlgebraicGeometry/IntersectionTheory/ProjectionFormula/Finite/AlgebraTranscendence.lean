import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! # Algebra Transcendence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.AlgebraTranscendence

noncomputable section

/-! A finite algebra map into a domain cannot increase transcendence
degree, even when the map has a nonzero kernel. -/

set_option backward.isDefEq.respectTransparency false

theorem le {K A B : Type} [Field K] [CommRing A] [CommRing B] [IsDomain B]
    [Algebra K A] [Algebra K B] (g : A →ₐ[K] B) (hg : g.Finite) :
    Algebra.trdeg K B ≤ Algebra.trdeg K A := by
  let P := g.range
  let := g.toRingHom.toAlgebra
  let := g.rangeRestrict.toRingHom.toAlgebra
  let : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite A B := hg
  let : Module.Finite P B := Module.Finite.of_restrictScalars_finite A P B
  have he := trdeg_add_eq K P (A := B)
  rw [trdeg_eq_zero (R := P) (A := B), add_zero] at he
  rw [← he]
  exact trdeg_le_of_surjective g.rangeRestrict g.rangeRestrict_surjective

theorem polynomial {K A : Type} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] {ι : Type} [Fintype ι]
    (g : MvPolynomial ι K →ₐ[K] A) (hg : g.Finite) :
    Algebra.trdeg K A ≤ Fintype.card ι := by
  simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_natCast]
    using le g hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.AlgebraTranscendence
