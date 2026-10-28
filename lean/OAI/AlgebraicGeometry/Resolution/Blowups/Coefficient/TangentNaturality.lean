import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.CenterDescent
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Tangent Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentNaturality.Construction

noncomputable section

/-! Intrinsic coefficient tangent centers agree under actual aligned étale comparisons. -/

universe u

def alignedHypersurfaceAlgHom {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) (z : R) (w : S) (h : f z = w) :
    (R ⧸ Ideal.span {z}) →ₐ[k] (S ⧸ Ideal.span {w}) where
  __ := Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z w h
  commutes' c := by
    change Ideal.Quotient.mk (Ideal.span {w}) (f (algebraMap k R c)) =
      Ideal.Quotient.mk (Ideal.span {w}) (algebraMap k S c)
    rw [f.commutes]

def coefficientTangentCenter (k : Type u) {R : Type u} [CommRing k] [CommRing R]
    [Algebra k R] (z : R) (J : Ideal R) (b n : ℕ) : Ideal R :=
  (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) n).comap
    (Ideal.Quotient.mk (Ideal.span {z}))

theorem coefficientTangentCenter_normal_mem
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (J : Ideal R) (b n : ℕ) : z ∈ coefficientTangentCenter k z J b n := by
  change Ideal.Quotient.mk (Ideal.span {z}) z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k _ n
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self z)]
  exact Ideal.zero_mem _

theorem coefficientTangentCenter_quotient
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (J : Ideal R) (b n : ℕ) :
    (coefficientTangentCenter k z J b n).map (Ideal.Quotient.mk (Ideal.span {z})) =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) n :=
  Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _

theorem coefficientTangentCenter_compared_quotients
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (z t : R) (heq : f z = g t)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] [Algebra.Smooth k (R ⧸ Ideal.span {t})]
    (J L : Ideal R) (b n : ℕ)
    (hcoeff : (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm)) :
    ((coefficientTangentCenter k z J b n).map (Ideal.Quotient.mk (Ideal.span {z}))).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      ((coefficientTangentCenter k t L b n).map (Ideal.Quotient.mk (Ideal.span {t}))).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm) := by
  rw [coefficientTangentCenter_quotient, coefficientTangentCenter_quotient]
  have hF := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k
    (alignedHypersurfaceAlgHom f z (f z) rfl) (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale f.toRingHom hf z (f z) rfl)
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) n
  have hG := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k
    (alignedHypersurfaceAlgHom g t (f z) heq.symm) (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap_etale g.toRingHom hg t (f z) heq.symm)
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b) n
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) n).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) = _ at hF
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b) n).map
      (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm) = _ at hG
  rw [hF, hG]
  exact congrArg (fun K => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k K n) hcoeff

/-- For these intrinsic centers, equality on the coefficient comparison is
proved by differential naturality, rather than supplied as another descent assumption. -/
theorem coefficientTangentCenter_compared_ambient_ideals
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (z t : R) (heq : f z = g t)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})] [Algebra.Smooth k (R ⧸ Ideal.span {t})]
    (J L : Ideal R) (b n : ℕ)
    (hcoeff : (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b).map
        (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm)) :
    (coefficientTangentCenter k z J b n).map f.toRingHom =
      (coefficientTangentCenter k t L b n).map g.toRingHom :=
  CenterDescent.Construction.aligned_hypersurface_center_equality f.toRingHom g.toRingHom z t heq _ _
    (coefficientTangentCenter_normal_mem k z J b n) (coefficientTangentCenter_normal_mem k t L b n)
    (coefficientTangentCenter_compared_quotients f g hf hg z t heq J L b n hcoeff)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentNaturality.Construction
