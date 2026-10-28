import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntertwiningBasis

/-! # Adapted Total -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdaptedTotal.CM

noncomputable section

section

/-! ThetaCycle: adapted period coordinates are preserved by the actual source
projector. Cross-coordinates of the native frames are independent of the
ball point, including the distinguished line and annihilator coordinates. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

theorem adapted_coordinates_paired (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool)
    (w : HeckeCycles.GeometricSource.CM.Ambient K) (p : HeckeCycles.GeometricSource.CM.Positions K places) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d w p =
      if p.1 = places.distinguished then
        if p.2 = 0 then (Symplectic.CM.galoisToPaired K places w p.1).1 2
        else (Symplectic.CM.galoisToPaired K places w p.1).2 (p.2 - 1)
      else if d (places.representative p.1) then (Symplectic.CM.galoisToPaired K places w p.1).2 p.2
      else (Symplectic.CM.galoisToPaired K places w p.1).1 p.2 := by
  simp only [Symplectic.CM.galoisToPaired_apply]
  rfl

theorem adapted_source_projector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (CompactComplex.CM.sourcePeriodProjector K B places d z w) =
      HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d w := by
  funext p
  rw [adapted_coordinates_paired, adapted_coordinates_paired, IntertwiningBasis.CM.paired_source_projector]
  rcases p with ⟨i, j⟩
  by_cases hi : i = places.distinguished
  · fin_cases j <;>
      simp [hi, CompactComplex.CM.distinguishedProjection, CompactComplex.CM.ballLineProjection, CompactComplex.CM.ballAnnihilatorProjection,
        HeckeCycles.GeometricSource.CM.BallDatum.lineVector]
  · cases d (places.representative i) <;> simp [hi]

theorem adapted_native_cross_frame_constant (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d e : Gal(K/ℚ) → Bool) (z t : HeckeCycles.GeometricSource.CM.BallChart) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (Prescribed.CM.nativePeriodFrame K B places e z x) =
      HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (Prescribed.CM.nativePeriodFrame K B places e t x) := by
  funext p
  simp only [adapted_coordinates_paired, Prescribed.CM.nativePeriodFrame, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rcases p with ⟨i, j⟩
  by_cases hi : i = places.distinguished
  · subst i
    fin_cases j <;>
      simp [RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame, Geometry.ComplexBall.PrescribedSignsB.globalFrame, Geometry.ComplexBall.PrescribedSignsB.placeFrame,
        Geometry.ComplexBall.PrescribedSignsB.localFrame, Geometry.ComplexBall.PrescribedSignsB.lineVector, Geometry.ComplexBall.PrescribedSignsB.axis]
  · cases d (places.representative i) <;> cases he : e (places.representative i) <;>
      simp [hi, he, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame, Geometry.ComplexBall.PrescribedSignsB.globalFrame, Geometry.ComplexBall.PrescribedSignsB.placeFrame]

theorem native_frame_recovers_line_graph {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Gal(K/ℚ) → Bool} (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    Prescribed.CM.nativePeriodFrame K B places d z
        (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) x)) =
      HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) x := by
  have hp : HeckeCycles.GeometricSource.CM.prescribed K B places d z (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) x) := by
    apply (L.graph_prescribed z hz _).mpr
    change (L.coordinates.complex (L.coordinates.complex.symm _)).1 =
      (L.period z).matrix.mulVec (L.coordinates.complex (L.coordinates.complex.symm _)).2
    rw [LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨u, hu⟩ := (CoefficientPeriods.CM.native_frame_range K B places d z _).mpr hp
  rw [← hu, Prescribed.CM.adapted_native_frame]

end

section

/-! ThetaCycle: a fixed change of multiplicity basis has constant coefficients
between the actual adapted native frames. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def adaptedPlace (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool) (p : HeckeCycles.GeometricSource.CM.Positions K places) : Gal(K/ℚ) :=
  if p.1 = places.distinguished then
    if p.2 = 0 then places.representative p.1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative p.1
  else if d (places.representative p.1) then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * places.representative p.1
  else places.representative p.1

omit [IsGalois ℚ K] in
theorem adapted_coordinates_fiber_sum {I : Type*} [Fintype I]
    (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool)
    (c : I → Gal(K/ℚ) → ℂ) (w : I → HeckeCycles.GeometricSource.CM.Ambient K) (p : HeckeCycles.GeometricSource.CM.Positions K places) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (fun τ j => ∑ i, c i τ * w i τ j) p =
      ∑ i, c i (adaptedPlace K places d p) * HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (w i) p := by
  simp only [HeckeCycles.GeometricSource.CM.adaptedCoordinates, LinearMap.coe_mk, AddHom.coe_mk, adaptedPlace]
  split_ifs <;> rfl

theorem adapted_fiber_change_native_constant {I : Type*} [Fintype I]
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool)
    (e : I → Gal(K/ℚ) → Bool) (c : I → Gal(K/ℚ) → ℂ)
    (x : I → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) (z t : HeckeCycles.GeometricSource.CM.BallChart) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d
        (fun τ j => ∑ i, c i τ * Prescribed.CM.nativePeriodFrame K B places (e i) z (x i) τ j) =
      HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d
        (fun τ j => ∑ i, c i τ * Prescribed.CM.nativePeriodFrame K B places (e i) t (x i) τ j) := by
  funext p
  rw [adapted_coordinates_fiber_sum, adapted_coordinates_fiber_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [adapted_native_cross_frame_constant K B places d (e i) z t]

theorem adapted_inverse_basis_native_constant
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Fin 2 → Gal(K/ℚ) → Bool)
    (e : Fin 2 → Gal(K/ℚ) → Bool) (b : Module.Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K))
    (x : Fin 2 → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) (z t : HeckeCycles.GeometricSource.CM.BallChart) (i : Fin 2) :
    HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d i)
        ((CompactComplex.CM.complexTensorBasisEquiv K b).symm (fun k => Prescribed.CM.nativePeriodFrame K B places (e k) z (x k)) i) =
      HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d i)
        ((CompactComplex.CM.complexTensorBasisEquiv K b).symm (fun k => Prescribed.CM.nativePeriodFrame K B places (e k) t (x k)) i) :=
  adapted_fiber_change_native_constant K B places (d i) e
    (fun k τ => (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) b)⁻¹ i k) x z t

end

/-! ThetaCycle: total native frames, adapted coordinates, and their literal
half-determinants for the two geometric line periods. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def totalAdaptedCoordinates (places : HeckeCycles.GeometricSource.CM.Places K) (d : Fin 2 → Gal(K/ℚ) → Bool) :
    ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] (PeriodTotal.CM.TotalPositions K places → ℂ) where
  toFun w := Sum.elim (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d 0) (w 0))
    (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d 1) (w 1))
  map_add' x y := by
    funext p
    cases p <;> simp
  map_smul' c x := by
    funext p
    cases p <;> simp

def totalNativePeriodFrame (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (PeriodTotal.CM.TotalPositions K places → ℂ) →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K where
  toFun x i := Prescribed.CM.nativePeriodFrame K B places (d i) z
    (fun p => x (if i = 0 then Sum.inl p else Sum.inr p))
  map_add' x y := by
    funext i
    exact map_add (Prescribed.CM.nativePeriodFrame K B places (d i) z) _ _
  map_smul' c x := by
    funext i
    exact map_smul (Prescribed.CM.nativePeriodFrame K B places (d i) z) c _

theorem total_adapted_native_frame (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    totalAdaptedCoordinates K places d (totalNativePeriodFrame K B places d z x) = x := by
  funext p
  cases p <;> simp [totalAdaptedCoordinates, totalNativePeriodFrame, Prescribed.CM.adapted_native_frame]

theorem total_adapted_source_projector (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) :
    totalAdaptedCoordinates K places d (TotalProjector.CM.totalSourceProjector K B places d z w) =
      totalAdaptedCoordinates K places d w := by
  funext p
  cases p with
  | inl p => exact congrFun (adapted_source_projector K B places (d 0) z (w 0)) p
  | inr p => exact congrFun (adapted_source_projector K B places (d 1) z (w 1)) p

theorem total_native_frame_recovers_graph {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d i))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    totalNativePeriodFrame K B places d z
        (totalAdaptedCoordinates K places d
          (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
            (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) x)) =
      TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
        (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) x := by
  rw [TotalPeriodGraphs.CM.total_block_graph]
  funext i
  fin_cases i
  · exact native_frame_recovers_line_graph K (L 0) z hz _
  · exact native_frame_recovers_line_graph K (L 1) z hz _

omit [IsGalois ℚ K] in
theorem total_adapted_graph_det {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (i : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d i))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    LinearMap.det ((totalAdaptedCoordinates K places d).comp
      (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
        (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)))) =
      (((L 0).halfDet z : ℂ) * ((L 1).halfDet z : ℂ)) ^ 2 := by
  let e := LinearEquiv.sumArrowLequivProdArrow (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ ℂ
  let f (i : Fin 2) := (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d i)).comp
    (HeckeCycles.GeometricSource.CM.graphInAmbient K (L i).coordinates ((L i).period z))
  have he : (totalAdaptedCoordinates K places d).comp
      (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (L i).coordinates)
        (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z))) =
      e.symm.toLinearMap.comp (((f 0).prodMap (f 1)).comp e.toLinearMap) := by
    apply LinearMap.ext
    intro x
    change totalAdaptedCoordinates K places d (TotalPeriodGraphs.CM.totalGraphInAmbient K _ _ x) = _
    rw [TotalPeriodGraphs.CM.total_block_graph]
    rfl
  rw [he]
  have hc : LinearMap.det (e.symm.toLinearMap.comp (((f 0).prodMap (f 1)).comp e.toLinearMap)) =
      LinearMap.det ((f 0).prodMap (f 1)) := by
    simpa only [LinearEquiv.symm_symm] using! LinearMap.det_conj ((f 0).prodMap (f 1)) e.symm
  rw [hc, LinearMap.det_prodMap, mul_pow]
  exact congrArg₂ (fun a b : ℂ => a * b) ((L 0).halfDet_square z hz).symm ((L 1).halfDet_square z hz).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdaptedTotal.CM
