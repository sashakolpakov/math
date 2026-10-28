import OAI.AlgebraicGeometry.Resolution.Blowups.PrincipalDifferentialSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.RegularHypersurfaceNormal
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Principal Differential Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.PrincipalDifferentialCriterion.Construction

noncomputable section

/-! The first differential ideal detects smoothness of a regular principal hypersurface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [IsNoetherianRing R]

theorem firstDifferential_principal_top_of_smooth_quotient
    (z : R) (hz : IsRegular z) [Algebra.Smooth k (R ⧸ Ideal.span {z})] :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z}) = ⊤ := by
  by_contra h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z})) h
  let : P.IsMaximal := hP
  have hzp : z ∈ P := hle (Relative.DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k _ (Ideal.mem_span_singleton_self z))
  obtain ⟨S, aS, hsS, f, hf, q, hq, E, hE⟩ :=
    RegularHypersurfaceNormal.Construction.smooth_regular_hypersurface_pointed_open_normal (k := k) z hz ⟨P, inferInstance⟩ hzp
  let : Algebra R S := f.toRingHom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  have hm : E (f z) ∈ (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z})).map f.toRingHom :=
    DifferentialNaturality.Construction.smooth_derivation_base_section_mem k (Ideal.span {z}) E z (Ideal.mem_span_singleton_self z)
  have hmap : (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z})).map f.toRingHom ≤ q.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    have he : q.asIdeal.comap f.toRingHom = P := congrArg PrimeSpectrum.asIdeal hq
    rw [he]
    exact hle
  exact q.isPrime.one_notMem (hE ▸ hmap hm)

theorem smooth_principal_quotient_iff_firstDifferential_top (z : R) (hz : IsRegular z) :
    Algebra.Smooth k (R ⧸ Ideal.span {z}) ↔ Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Ideal.span {z}) = ⊤ := by
  constructor
  · intro h
    let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := h
    exact firstDifferential_principal_top_of_smooth_quotient k z hz
  · exact PrincipalDifferentialSmoothness.Construction.smooth_principal_quotient_of_firstDifferential_top k z

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.PrincipalDifferentialCriterion.Construction
