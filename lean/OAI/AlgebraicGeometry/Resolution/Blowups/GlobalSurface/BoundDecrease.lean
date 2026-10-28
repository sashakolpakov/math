import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.PointedBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.CenterBlowupSmooth
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentBoundCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ChoiceEtaleMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Homogenization

/-! # Bound Decrease -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The actual global canonical surface step decreases the common coefficient bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.surfaceCenter_homogenized_transform_bound (ℓ : ℕ)
    (hb : ∀ i, (A.choice i).HasBound (ℓ + 1))
    (hd : ∀ i, ringKrullDim (A.rings i) ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (B : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas
      (GlobalBlowup.Data.Construction.globalBlowupToBase (A.surfaceCenter ℓ hb hd hlevel) (A.surfaceCenter_nonzero ℓ hb hd hlevel) ≫ f)
      (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (A.surfaceCenter ℓ hb hd hlevel)
        (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n) (A.surfaceCenter_nonzero ℓ hb hd hlevel) (n + 1)) n) :
    ∀ i, (B.choice i).HasBound ℓ := by
  let I := A.surfaceCenter ℓ hb hd hlevel
  let hI : I ≠ ⊥ := A.surfaceCenter_nonzero ℓ hb hd hlevel
  let H := Global.Homogenization.Construction.smoothHomogenizedIdealSheaf f J n
  have hp : H ≤ I ^ (n + 1) := (Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_permissible_iff f I J n).mpr
    (A.surfaceCenter_isPermissible ℓ hb hd hlevel)
  let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := A.surfaceCenter_isBlowupSmooth ℓ hb hd hlevel
  apply GlobalBlowup.PointedBounds.Construction.globalBlowup_hasBound_of_generating_neighborhoods f I H hI n ℓ hp B
  intro x
  obtain ⟨i, p, hp⟩ := Global.MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec A.nativeOpens A.nativeOpens_cover x
  let U := A.nativeOpens i
  let R := Γ(X, U)
  change PrimeSpectrum R at p
  let : Algebra ℂ R := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℚ R := ((algebraMap ℂ R).comp (algebraMap ℚ ℂ)).toAlgebra
  let : Algebra.Smooth ℂ R := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let e := Affine.OpenBoundaryTransport.Construction.specOpenSectionAlgEquiv f (A.rings i) (A.map i) (A.ground i)
  let C := (A.choice i).toSurfaceTangentChoice ℓ (hb i)
  let C' := C.mapEtale e.symm.toAlgHom (RingHom.Etale.of_bijective e.symm.bijective)
  have hJ : J.ideal U = (A.ideals i).map e.symm.toRingHom := by
    rw [Affine.OpenBoundaryTransport.Construction.specOpenSectionEquiv_ideal (A.rings i) (A.map i) J _ (A.ideal_eq i)]
    exact (Ideal.map_symm e.toRingEquiv).symm
  have hC : C'.center = I.ideal U := by
    rw [Surface.TangentCenterChoice.Construction.SurfaceTangentCenterChoice.center_map_etale,
      A.surfaceCenter_ideal ℓ (fun i => (A.choice i).toSurfaceTangentChoice ℓ (hb i)) I
        (A.surfaceCenter_restrict ℓ hb hd hlevel) i]
    exact Ideal.map_symm e.toRingEquiv
  have hH : Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ ((A.ideals i).map e.symm.toRingHom) n = H.ideal U := by
    rw [Global.Homogenization.Construction.smoothHomogenizedIdealSheaf_ideal, hJ]
  change Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ ((A.ideals i).map e.symm.toAlgHom.toRingHom) n = H.ideal U at hH
  have hdR : ringKrullDim R ≤ 2 := e.toRingEquiv.ringKrullDim.le.trans (hd i)
  have hex := C'.exists_pointed_bounded_blowup_generators hdR hlevel p
  rw [hC, hH] at hex
  obtain ⟨S, akS, aqS, hsS, φ, hφ, Q, hQ, κ, g, hgen, hbound⟩ := hex
  refine ⟨U, S, akS, aqS, hsS, φ, hφ, Q, ?_, κ, g, hgen, hbound⟩
  change U.2.fromSpec (PrimeSpectrum.comap φ.toRingHom Q) = x
  rw [hQ]
  exact hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups
