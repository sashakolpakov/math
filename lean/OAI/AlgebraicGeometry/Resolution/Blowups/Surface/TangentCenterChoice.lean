import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterOverlap

/-! # Tangent Center Choice -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterChoice.Construction

noncomputable section

/-! Fixed-level canonical tangent-center choices on smooth surface charts, including terminal charts. -/

universe u

inductive SurfaceTangentCenterChoice (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (J : Ideal R) (n ℓ : ℕ) : Type u
  | terminal (h : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤)
  | normal (z : R) (D : Derivation k R R) (hD : D z = 1)
      (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
      (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
        (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤)

namespace SurfaceTangentCenterChoice
section

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n ℓ : ℕ}

def center : SurfaceTangentCenterChoice k R J n ℓ → Ideal R
  | .terminal _ => ⊤
  | .normal z _ _ _ _ => Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ

end

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    {J : Ideal R} {n ℓ : ℕ}

omit [CharZero k] in
theorem permissible (C : SurfaceTangentCenterChoice k R J n ℓ)
    (hdim : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) : J ≤ C.center ^ (n + 1) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  cases C with
  | terminal _ => simp only [SurfaceTangentCenterChoice.center, Ideal.top_pow]; exact le_top
  | normal z D hD _ hbound =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      have hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 1 := NormalQuotientDimension.Construction.normal_quotient_dimension_induction D z hD 1 hdim
      exact (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n).trans
        (Coefficient.TangentCurveCenter.Construction.coefficientTangentCenter_curve_permissible k D z hD
          (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ hd hlevel hbound).1

omit [CharZero k] in
theorem tangent_le (C : SurfaceTangentCenterChoice k R J n ℓ)
    (hdim : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ C.center :=
  Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J C.center n (C.permissible hdim hlevel)

theorem center_eq_on_common_refinement
    {A S : Type u} [CommRing A] [CommRing S] [Algebra k A] [Algebra k S]
    [Algebra ℚ A] [Algebra.Smooth k A]
    (f : R →ₐ[k] S) (g : A →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    {L : Ideal A} (hJL : J.map f.toRingHom = L.map g.toRingHom)
    (C : SurfaceTangentCenterChoice k R J n ℓ) (B : SurfaceTangentCenterChoice k A L n ℓ)
    (hdR : ringKrullDim R ≤ 2) (hdA : ringKrullDim A ≤ 2)
    (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    C.center.map f.toRingHom = B.center.map g.toRingHom := by
  have hT : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n).map g.toRingHom := by
    rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf,
      Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k g hg, hJL]
  cases C with
  | terminal ht =>
      have h := Ideal.map_mono (f := g.toRingHom) (B.tangent_le hdA hlevel)
      rw [← hT, ht, Ideal.map_top] at h
      exact (Ideal.map_top f.toRingHom).trans (top_le_iff.mp h).symm
  | normal z D hD hz hbz =>
      cases B with
      | terminal ht =>
          have h := Ideal.map_mono (f := f.toRingHom)
            (SurfaceTangentCenterChoice.tangent_le (normal z D hD hz hbz : SurfaceTangentCenterChoice k R J n ℓ) hdR hlevel)
          rw [hT, ht, Ideal.map_top] at h
          exact (top_le_iff.mp h).trans (Ideal.map_top g.toRingHom).symm
      | normal t E hE ht hbt =>
          exact TangentCenterOverlap.Construction.surface_coefficient_tangent_centers_agree_on_common_refinement k f g hf hg J L hJL n ℓ
            z t D E hD hE hz ht hdR hlevel hbz hbt

end SurfaceTangentCenterChoice

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterChoice.Construction
