import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.CoordinateSubspaceModel
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SmoothCenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.IdealSheafIdentification
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhoodBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.KernelZero

/-! # Coordinate Subspace Chart Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChartExistence.Construction

noncomputable section

/-! Smooth points of a nonzero closed ideal in an integral smooth ambient scheme have retained integral coordinate-subspace charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_coordinate_subspace_chart
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    [Smooth (J.subschemeι ≫ f)] (x : X) (hx : x ∈ J.support) :
    Nonempty (CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J x) := by
  classical
  obtain ⟨O, hO, hxO, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let U : X.affineOpens := ⟨O, hO⟩
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  let : Algebra.Smooth ℂ (Γ(X, U) ⧸ J.ideal U) := SmoothCenterBlowup.Construction.idealSheaf_complex_smooth_center_quotient f J U
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hxrange : x ∈ U.2.fromSpec.opensRange := by rw [U.2.opensRange_fromSpec]; exact hxO
  obtain ⟨p, hp⟩ := hxrange
  have hJp : J.ideal U ≤ p.asIdeal := by
    apply (Coefficient.ChartSupport.Construction.affine_center_le_prime_iff_global_support J _ U.2.fromSpec (J.ideal U)
      (Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel J U) p).mpr
    rwa [hp]
  obtain ⟨S, hSalg, hSsmooth, φ, hφ, q, hq, ι, hι, hdec, n, ψ, hψ, hI⟩ :=
    Pointed.CoordinateSubspaceModel.Construction.exists_pointed_coordinate_subspace_open_model (k := ℂ) (J.ideal U) p hJp
  let : Algebra ℂ S := hSalg
  let : Algebra.Smooth ℂ S := hSsmooth
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := hφ
  let j := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ U.2.fromSpec
  have hg : j ≫ f = ComplexAffineDifferentialIdeal.Construction.complexSpecStructure S := by
    dsimp only [j]
    rw [Category.assoc, ← Affine.ComplexNaturality.Construction.affineComplexScalars_spec f U, ← Spec.map_comp]
    apply congrArg Spec.map
    ext c
    exact φ.commutes c
  have hjq : j q = x := by
    change U.2.fromSpec (PrimeSpectrum.comap φ.toRingHom q) = x
    rw [hq]
    exact hp
  have he : J.comap j = Affine.QuotientKernel.Construction.affineQuotientKernel
      ((RingHom.ker Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection.toRingHom).map ψ.toRingHom) := by
    rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_affineMap_eq_quotient_kernel, hI]
  let : Nonempty (Spec S) := ⟨q⟩
  let : IsIntegral (Spec S) := isIntegral_of_isOpenImmersion j
  have hmodel : RingHom.ker (Coordinate.SubspaceIdeal.Construction.polynomialCoordinateProjection (σ := ι) (τ := Fin n) (R := ℂ)).toRingHom ≠ ⊥ := by
    intro hz
    have hnonzero := ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot j J hJ
    apply hnonzero
    rw [he, hz, Ideal.map_bot, Affine.KernelZero.Construction.affineQuotientKernel_bot]
  exact ⟨{ ring := S
           algebra := hSalg
           smooth := hSsmooth
           domain := (affine_isIntegral_iff S).mp inferInstance
           map := j
           isOpenImmersion := inferInstance
           ground := hg
           point := q
           point_over := hjq
           normal := ι
           normalFinite := hι
           normalDecidableEq := hdec
           freeDimension := n
           coordinate := ψ
           coordinate_etale := hψ
           modelNonzero := hmodel
           ideal_eq := he }⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChartExistence.Construction
