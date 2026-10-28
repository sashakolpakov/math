import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.RegularHypersurfaceNormal
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterNormalFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface

/-! # Hypersurface Normal Frames -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.HypersurfaceNormalFrames.Construction

noncomputable section

/-! Actual pointed common normal frames for a smooth center contained in a smooth regular hypersurface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smooth_hypersurface_center_pointed_normal_frame
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (z : R) (hz : IsRegular z) [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    (hzI : z ∈ I) (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
        (v : Option ι → S) (D : Option ι → Derivation k S S),
        (∀ i j, D i (v j) = if i = j then 1 else 0) ∧
        v none = f z ∧ I.map f.toRingHom = Ideal.span (Set.range v) := by
  obtain ⟨A, aA, hsA, φ, hopen, pA, hpA, E, hE⟩ :=
    RegularHypersurfaceNormal.Construction.smooth_regular_hypersurface_pointed_open_normal (k := k) z hz p (hIp hzI)
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hopen
  have hφ : φ.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom φ.toRingHom)).mp inferInstance
  let : Algebra R A := φ.toRingHom.toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let : Algebra.Etale R A := RingHom.etale_algebraMap.mp hφ
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let : Algebra.Smooth k (A ⧸ I.map φ.toRingHom) := TransformedCoordinateHypersurface.Construction.smooth_etale_extended_quotient I
  have hIA : I.map φ.toRingHom ≤ pA.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have he : pA.asIdeal.comap φ.toRingHom = p.asIdeal := congrArg PrimeSpectrum.asIdeal hpA
    rwa [he]
  obtain ⟨S, aS, hsS, ψ, hopenS, q, hq, ι, hι, hdec, v, D, hD, hv, hgen⟩ :=
    CenterNormalFrame.Construction.smooth_center_pointed_open_frame_retaining_normal (k := k) (I.map φ.toRingHom) (φ z)
      (Ideal.mem_map_of_mem _ hzI) E hE pA hIA
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := hopenS
  refine ⟨S, aS, hsS, ψ.comp φ, ?_, q, ?_, ι, hι, hdec, v, D, hD, hv, ?_⟩
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom ψ.toRingHom))
    rw [Spec.map_comp]
    infer_instance
  · apply PrimeSpectrum.ext
    change (q.asIdeal.comap ψ.toRingHom).comap φ.toRingHom = p.asIdeal
    have he : q.asIdeal.comap ψ.toRingHom = pA.asIdeal := congrArg PrimeSpectrum.asIdeal hq
    rw [he]
    exact congrArg PrimeSpectrum.asIdeal hpA
  · change I.map (ψ.toRingHom.comp φ.toRingHom) = _
    rw [← Ideal.map_map]
    exact hgen

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.HypersurfaceNormalFrames.Construction
