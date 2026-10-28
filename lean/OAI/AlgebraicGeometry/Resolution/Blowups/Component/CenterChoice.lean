import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterOverlap

/-! # Center Choice -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterChoice.Construction

noncomputable section

/-! Local canonical component-center data, including charts outside the order locus. -/

universe u

inductive ComponentCenterChoice (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (J : Ideal R) (n : ℕ) : Type u
  | terminal (h : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n = ⊤)
  | normal (z : R) (D : Derivation k R R) (hD : D z = 1)
      (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)

namespace ComponentCenterChoice
section

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J : Ideal R} {n : ℕ}

def center : ComponentCenterChoice k R J n → Ideal R
  | .terminal _ => ⊤
  | .normal z _ _ _ => Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)

end

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    {J : Ideal R} {n : ℕ}

theorem permissible (C : ComponentCenterChoice k R J n) : J ≤ C.center ^ (n + 1) := by
  cases C with
  | terminal _ => simp only [ComponentCenterChoice.center, Ideal.top_pow]; exact le_top
  | normal z D hD _ =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      exact (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n).trans
        (Coefficient.Component.Construction.coefficientComponentCenter_permissible k D z hD (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1))

theorem tangent_le (C : ComponentCenterChoice k R J n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ C.center :=
  Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J C.center n C.permissible

theorem center_eq_on_common_refinement
    {A S : Type u} [CommRing A] [CommRing S] [Algebra k A] [Algebra k S]
    [Algebra ℚ A] [Algebra.Smooth k A]
    (f : R →ₐ[k] S) (g : A →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    {L : Ideal A} (hJL : J.map f.toRingHom = L.map g.toRingHom)
    (C : ComponentCenterChoice k R J n) (B : ComponentCenterChoice k A L n) :
    C.center.map f.toRingHom = B.center.map g.toRingHom := by
  have hT : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n).map g.toRingHom := by
    rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf,
      Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k g hg, hJL]
  cases C with
  | terminal ht =>
      have h := Ideal.map_mono (f := g.toRingHom) B.tangent_le
      rw [← hT, ht, Ideal.map_top] at h
      exact (Ideal.map_top f.toRingHom).trans (top_le_iff.mp h).symm
  | normal z D hD hz =>
      cases B with
      | terminal ht =>
          have h := Ideal.map_mono (f := f.toRingHom)
            (ComponentCenterChoice.tangent_le (normal z D hD hz : ComponentCenterChoice k R J n))
          rw [hT, ht, Ideal.map_top] at h
          exact (top_le_iff.mp h).trans (Ideal.map_top g.toRingHom).symm
      | normal t E hE ht =>
          exact CenterOverlap.Construction.coefficient_component_centers_agree_on_common_refinement k f g hf hg J L hJL n
            z t D E hD hE hz ht

end ComponentCenterChoice

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterChoice.Construction
