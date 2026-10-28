import OAI.AlgebraicGeometry.Resolution.Blowups.FixedNormalBoundaryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ModeledCoordinateRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Dimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Normal Line Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.NormalLineNeighborhood.Construction

noncomputable section

/-! A specified smooth normal equation admits a pointed étale-line retraction with one smaller coefficient dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_smooth_normal_line_neighborhood
    (k : Type u) [Field k] [CharZero k] {R : Type u} [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (z : R) (D : Derivation k R R) (hD : D z = 1)
    (q : PrimeSpectrum R) (hzq : z ∈ q.asIdeal) (d : ℕ) (hd : ringKrullDim R ≤ (d + 1 : ℕ)) :
    ∃ (H : CommRingCat.{u}) (_ : Algebra k H) (_ : Algebra.Smooth k H),
      ringKrullDim H ≤ d ∧
      ∃ (V : CommRingCat.{u}) (_ : Algebra k V) (_ : Algebra H V) (_ : Algebra (Polynomial H) V),
        IsScalarTower k H V ∧ IsScalarTower H (Polynomial H) V ∧ Algebra.Etale (Polynomial H) V ∧
        ∃ g : R →ₐ[k] V, g.toRingHom.Etale ∧
          g z = algebraMap (Polynomial H) V Polynomial.X ∧
          ∃ _e : (V ⧸ Ideal.span {algebraMap (Polynomial H) V Polynomial.X}) ≃ₐ[H] H,
            ∃ Q : PrimeSpectrum V, PrimeSpectrum.comap g.toRingHom Q = q := by
  classical
  let : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨s, hs, r, pAlg, htor, het⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q.asIdeal)
  let S := Localization.Away s
  let : Algebra (MvPolynomial (Fin r) k) S := pAlg
  let : IsScalarTower k (MvPolynomial (Fin r) k) S := htor
  let : Algebra.IsStandardEtale (MvPolynomial (Fin r) k) S := het
  let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway s
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let E := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D
  have hE : E (f z) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D (algebraMap R S z) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD, map_one]
  let P := MvPolynomial (Fin r) k
  let ε := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
  let φ := (algebraMap P S).comp ε.toRingHom
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition ε.toRingHom (algebraMap P S)
    (RingHom.Etale.of_bijective ε.bijective) (RingHom.etale_algebraMap.mpr inferInstance)
  have hφk (c : k) : φ (MvPolynomial.C c) = algebraMap k S c := by
    change algebraMap P S (MvPolynomial.rename (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r) (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C]
    exact (IsScalarTower.algebraMap_apply k P S c).symm
  let w : Empty → S := Empty.elim
  let M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k S Empty w := {
    indices := ULift.{u} (Fin r)
    finite := inferInstance
    decidableEq := inferInstance
    map := φ
    etale := hφ
    ground := hφk
    coordinate := Empty.elim
    distinct := fun i => Empty.elim i
    multiplier := Empty.elim
    multiplierUnit := fun i => Empty.elim i
    equation := fun i => Empty.elim i }
  obtain ⟨qS, hqS⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s q hs
  have hzS : f z ∈ qS.asIdeal := by
    have he : qS.asIdeal.comap f.toRingHom = q.asIdeal := congrArg PrimeSpectrum.asIdeal hqS
    change z ∈ qS.asIdeal.comap f.toRingHom
    rw [he]
    exact hzq
  obtain ⟨C⟩ := FixedNormalBoundaryOpen.Construction.exists_fixed_normal_boundary_open (.of S) w M E (fun i => Empty.elim i) (f z) hE qS
  let A := C.chart.carrier
  let g₀ : R →ₐ[k] A := C.chart.map.comp f
  have hC : C.chart.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom C.chart.map.toRingHom)).mp inferInstance
  have hg₀ : g₀.toRingHom.Etale := RingHom.Etale.stableUnderComposition f.toRingHom C.chart.map.toRingHom hf hC
  have hzA : C.chart.map (f z) ∈ C.chart.point.asIdeal := by
    have he : C.chart.point.asIdeal.comap C.chart.map.toRingHom = qS.asIdeal :=
      congrArg PrimeSpectrum.asIdeal C.chart.point_over
    change f z ∈ C.chart.point.asIdeal.comap C.chart.map.toRingHom
    rw [he]
    exact hzS
  let : Algebra (MvPolynomial C.chart.model.indices k) A := C.chart.model.map.toAlgebra
  let : Algebra.Etale (MvPolynomial C.chart.model.indices k) A := RingHom.etale_algebraMap.mp C.chart.model.etale
  let : IsScalarTower k (MvPolynomial C.chart.model.indices k) A :=
    IsScalarTower.of_algebraMap_eq (fun c => (C.chart.model.ground c).symm)
  let H := MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := A) C.normalIndex
  let : Algebra.Smooth k H := Coordinate.RetractionDimension.Construction.coordinateLineFiber_smooth C.normalIndex
  have hdA : ringKrullDim A ≤ (d + 1 : ℕ) := (Blowups.Etale.Dimension.Construction.ringKrullDim_le_of_etale g₀.toRingHom hg₀).trans hd
  have hdH : ringKrullDim H ≤ d := Coordinate.RetractionDimension.Construction.coordinateLineFiber_dimension_induction C.normalIndex d hdA
  obtain ⟨V, cV, akV, aHV, aHPV, hkHV, hHPV, heV, g, hg, hnormal, e, _, _, _, _, Q, hQ, _⟩ :=
    Pointed.ModeledCoordinateRetraction.Construction.exists_pointed_modeled_coordinate_retraction C.chart.model C.normalIndex C.normal_unused
      (C.chart.map (f z)) C.normal_eq C.chart.point hzA
  let h : R →ₐ[k] V := g.comp g₀
  have hh : h.toRingHom.Etale := RingHom.Etale.stableUnderComposition g₀.toRingHom g.toRingHom hg₀ hg
  refine ⟨.of H, inferInstance, inferInstance, hdH, .of V, akV, aHV, aHPV, hkHV, hHPV, heV,
    h, hh, hnormal, e, Q, ?_⟩
  change PrimeSpectrum.comap f.toRingHom
    (PrimeSpectrum.comap C.chart.map.toRingHom (PrimeSpectrum.comap g.toRingHom Q)) = q
  rw [hQ, C.chart.point_over]
  exact hqS

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.NormalLineNeighborhood.Construction
