import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.NormalLineNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.IntrinsicTangentBoundCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentBaseChange

/-! # Surface Tangent Bound Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.SurfaceTangentBoundCover.Construction

noncomputable section

/-! A pointed normal neighborhood realizes the canonical surface tangent center and the strict bound drop. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem exists_pointed_normal_tangent_bound_cover
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    (J : Ideal R) (n ℓ : ℕ) (z : R) (D : Derivation k R R) (hD : D z = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤)
    (hd : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (p : PrimeSpectrum R) (hzp : z ∈ p.asIdeal) :
    let I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra ℚ S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), f.toRingHom.Etale ∧
      ∃ Q : PrimeSpectrum S, PrimeSpectrum.comap f.toRingHom Q = p ∧
      ∃ (κ : Type u) (g : κ → I.map f.toRingHom),
        Ideal.span (Set.range (fun a => (g a).val)) = I.map f.toRingHom ∧
        ∀ a, ∃ B : Component.CenterChoice.Construction.ComponentCenterChoice k (Blowup.Charts.Construction.blowupChart (I.map f.toRingHom) (g a))
          (ControlledTransform.Construction.blowupControlledTransform (I.map f.toRingHom)
            ((Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom) (n + 1) (g a)) n, B.HasBound ℓ := by
  let I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
  obtain ⟨H, akH, hsH, hdH, S, akS, aHS, aHPS, hkHS, hHPS, heS, f, hf, hfz, e, Q, hQ⟩ :=
    Blowups.Smooth.NormalLineNeighborhood.Construction.exists_smooth_normal_line_neighborhood k z D hD p hzp 1 hd
  let : Algebra k H := akH
  let : Algebra.Smooth k H := hsH
  let : Algebra k S := akS
  let : Algebra H S := aHS
  let : Algebra (Polynomial H) S := aHPS
  let : IsScalarTower k H S := hkHS
  let : IsScalarTower H (Polynomial H) S := hHPS
  let : Algebra.Etale (Polynomial H) S := heS
  let : Algebra ℚ S := ((algebraMap k S).comp (algebraMap ℚ k)).toAlgebra
  let : Algebra.Smooth k S := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k f hf
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let L := (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom
  let w := algebraMap (Polynomial H) S Polynomial.X
  have hzL : w ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n := by
    dsimp only [w, L]
    rw [← hfz, ← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]
    apply Ideal.mem_map_of_mem
    rwa [HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
  have hbL : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k w L (n + 1)) (ℓ + 1) = ⊤ := by
    have hc := Coefficient.TangentBaseChange.Construction.coefficientTangentCenter_map_etale k f hf z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) (ℓ + 1)
    have ht : Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) (ℓ + 1) = ⊤ := by
      unfold Coefficient.TangentNaturality.Construction.coefficientTangentCenter
      rw [hbound, Ideal.comap_top]
    rw [ht, Ideal.map_top, hfz] at hc
    have hq := Coefficient.TangentNaturality.Construction.coefficientTangentCenter_quotient k w L (n + 1) (ℓ + 1)
    rw [← hc, Ideal.map_top] at hq
    exact hq.symm
  have hIL : I.map f.toRingHom = Coefficient.TangentNaturality.Construction.coefficientTangentCenter k w L (n + 1) ℓ := by
    dsimp only [I, w, L]
    rw [Coefficient.TangentBaseChange.Construction.coefficientTangentCenter_map_etale k f hf, hfz]
  have hc := EtaleLine.IntrinsicTangentBoundCover.Construction.etaleLine_intrinsic_tangent_bounded_generators k e L n ℓ hzL hdH hlevel hbL
  change ∃ (κ : Type u) (g : κ → Coefficient.TangentNaturality.Construction.coefficientTangentCenter k w L (n + 1) ℓ), _ at hc
  rw [← hIL] at hc
  exact ⟨S, akS, inferInstance, inferInstance, f, hf, Q, hQ, hc⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.SurfaceTangentBoundCover.Construction
