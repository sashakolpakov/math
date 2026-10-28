import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialSaturation

/-! # Component Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentNaturality.Construction

noncomputable section

/-! Canonical coefficient component centers and their aligned étale comparison. -/

universe u

def coefficientComponentCenter (k : Type u) {R : Type u} [CommRing k] [CommRing R]
    [Algebra k R] (z : R) (J : Ideal R) (b : ℕ) : Ideal R :=
  (DifferentialSaturation.Construction.relativeDifferentialSaturation k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)).comap
    (Ideal.Quotient.mk (Ideal.span {z}))

theorem coefficientComponentCenter_normal_mem
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (J : Ideal R) (b : ℕ) : z ∈ coefficientComponentCenter k z J b := by
  change Ideal.Quotient.mk (Ideal.span {z}) z ∈ DifferentialSaturation.Construction.relativeDifferentialSaturation k _
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
  exact Ideal.zero_mem _

theorem coefficientComponentCenter_quotient
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (J : Ideal R) (b : ℕ) :
    (coefficientComponentCenter k z J b).map (Ideal.Quotient.mk (Ideal.span {z})) =
      DifferentialSaturation.Construction.relativeDifferentialSaturation k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) :=
  Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

theorem coefficientComponentCenter_compared_quotients
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (z t : R) (heq : f z = g t)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] [Algebra.Smooth k (R ⧸ Ideal.span {t})]
    (J L : Ideal R) (b : ℕ)
    (hcoeff : (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm)) :
    ((coefficientComponentCenter k z J b).map (Ideal.Quotient.mk (Ideal.span {z}))).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      ((coefficientComponentCenter k t L b).map (Ideal.Quotient.mk (Ideal.span {t}))).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm) := by
  rw [coefficientComponentCenter_quotient, coefficientComponentCenter_quotient]
  have hF := DifferentialSaturation.Construction.relativeDifferentialSaturation_map k
    (TangentNaturality.Construction.alignedHypersurfaceAlgHom f z (f z) rfl) (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale f.toRingHom hf z (f z) rfl)
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)
  have hG := DifferentialSaturation.Construction.relativeDifferentialSaturation_map k
    (TangentNaturality.Construction.alignedHypersurfaceAlgHom g t (f z) heq.symm) (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale g.toRingHom hg t (f z) heq.symm)
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b)
  change (DifferentialSaturation.Construction.relativeDifferentialSaturation k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b)).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) = _ at hF
  change (DifferentialSaturation.Construction.relativeDifferentialSaturation k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b)).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm) = _ at hG
  rw [hF, hG]
  exact congrArg (fun K => DifferentialSaturation.Construction.relativeDifferentialSaturation k K) hcoeff

/-- For these intrinsic centers, equality on the coefficient comparison is
proved by differential naturality, rather than supplied as another descent assumption. -/
theorem coefficientComponentCenter_compared_ambient_ideals
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (z t : R) (heq : f z = g t)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] [Algebra.Smooth k (R ⧸ Ideal.span {t})]
    (J L : Ideal R) (b : ℕ)
    (hcoeff : (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm)) :
    (coefficientComponentCenter k z J b).map f.toRingHom =
      (coefficientComponentCenter k t L b).map g.toRingHom :=
  CenterDescent.Construction.aligned_hypersurface_center_equality f.toRingHom g.toRingHom z t heq _ _
    (coefficientComponentCenter_normal_mem k z J b) (coefficientComponentCenter_normal_mem k t L b)
    (coefficientComponentCenter_compared_quotients f g hf hg z t heq J L b hcoeff)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentNaturality.Construction
