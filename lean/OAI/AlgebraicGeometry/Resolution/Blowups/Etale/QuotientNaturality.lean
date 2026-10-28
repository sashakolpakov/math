import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Hypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.EtaleNaturality

/-! # Quotient Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.QuotientNaturality.Construction

noncomputable section

/-! Étale comparison maps on the actual aligned hypersurface quotients. -/

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A map to a specified hypersurface quotient, with the equation alignment
recorded explicitly. -/
def alignedHypersurfaceMap (f : R →+* S) (z : R) (w : S) (h : f z = w) :
    (R ⧸ Ideal.span {z}) →+* (S ⧸ Ideal.span {w}) :=
  Ideal.quotientMap (Ideal.span {w}) f
    ((Ideal.span_singleton_le_iff_mem _).mpr (by
      change f z ∈ Ideal.span {w}
      rw [h]
      exact Ideal.mem_span_singleton_self w))

theorem alignedHypersurfaceMap_mk (f : R →+* S) (z : R) (w : S) (h : f z = w)
    (x : R) :
    alignedHypersurfaceMap f z w h (Ideal.Quotient.mk (Ideal.span {z}) x) =
      Ideal.Quotient.mk (Ideal.span {w}) (f x) := rfl

/-- Aligned hypersurface comparison maps are étale, by actual quotient
base change and the quotient isomorphism given by the aligned equations. -/
theorem alignedHypersurfaceMap_etale (f : R →+* S) (hf : f.Etale)
    (z : R) (w : S) (h : f z = w) : (alignedHypersurfaceMap f z w h).Etale := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.Etale R S := hf
  let I := Ideal.span {z}
  have hI : I.map f = Ideal.span {w} := by
    simp only [I, Ideal.map_span, Set.image_singleton, h]
  let e := Ideal.quotEquivOfEq hI
  let : Algebra.Etale (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := Coordinate.Hypersurface.Construction.etale_quotient_of_etale I
  have hquot : (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  have heq : alignedHypersurfaceMap f z w h =
      e.toRingHom.comp (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))) := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  rw [heq]
  exact RingHom.Etale.stableUnderComposition _ e.toRingHom
    hquot (RingHom.Etale.of_bijective e.bijective)

variable {σ k : Type u} [Field k] [Algebra k R] [Algebra k S]
  [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
  [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]

include σ in
/-- Intrinsic coefficient ideals commute with a raw étale map into the
aligned hypersurface, without a supplied coordinate presentation on the target. -/
theorem relativeCoefficientIdeal_map_aligned_etale (f : R →ₐ[k] S)
    (hf : f.toRingHom.Etale) (z : R) (w : S) (h : f z = w) (J : Ideal R) (b : ℕ) :
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map (alignedHypersurfaceMap f.toRingHom z w h) =
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k w (J.map f.toRingHom) b := by
  unfold Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  apply congrArg (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b)
  funext j
  rw [Ideal.map_map]
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map
      ((Ideal.Quotient.mk (Ideal.span {w})).comp f.toRingHom) = _
  rw [← Ideal.map_map, Relative.EtaleNaturality.Construction.relativeDifferentialIdeal_map_etale (σ := σ) f hf]

include σ in
/-- When two ambient ideals and hypersurface equations agree on an étale
comparison chart, their coefficient ideals agree on its actual hypersurface. -/
theorem relativeCoefficientIdeal_comparison_eq (f g : R →ₐ[k] S)
    (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    (z t : R) (heq : f z = g t) (J L : Ideal R)
    (hJL : J.map f.toRingHom = L.map g.toRingHom) (b : ℕ) :
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map (alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t L b).map
        (alignedHypersurfaceMap g.toRingHom t (f z) heq.symm) := by
  rw [relativeCoefficientIdeal_map_aligned_etale (σ := σ) f hf,
    relativeCoefficientIdeal_map_aligned_etale (σ := σ) g hg, hJL]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.QuotientNaturality.Construction
