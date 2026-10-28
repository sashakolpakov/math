import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.SurfaceOrderTree
import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedDerivativeNeighborhood

/-! # Order Open Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.OrderOpenChart.Construction

noncomputable section

/-! Actual open order-reduction charts around derivative points of a smooth surface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure SurfaceOrderOpenChart (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (J : Ideal R) (b : ℕ) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  tree : Blowups.Smooth.AffineEtaleControlTree.Construction.SmoothAffineEtaleControlTree k b carrier (J.map map.toRingHom)

attribute [instance] SurfaceOrderOpenChart.algebra SurfaceOrderOpenChart.isOpenImmersion

def SurfaceOrderOpenChart.openRange {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {J : Ideal R} {b : ℕ} (C : SurfaceOrderOpenChart k R J b) : TopologicalSpace.Opens (PrimeSpectrum R) :=
  (Spec.map (CommRingCat.ofHom C.map.toRingHom)).opensRange

variable (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
  (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R]

/-- A nonvanishing derivative of an actual maximal-contact section gives
an affine open order-reduction chart containing the specified original point.
The equation is retained through both principal localizations and coordinate adaptation. -/
theorem surface_derivative_order_open_chart (hd : ringKrullDim R ≤ 2)
    (J : Ideal R) (n : ℕ) (D : Derivation k R R) (z : R)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (q : PrimeSpectrum R) (hDz : D z ∉ q.asIdeal) :
    ∃ C : SurfaceOrderOpenChart k R J (n + 1), q ∈ C.openRange := by
  let A := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime (D z) q hDz
  obtain ⟨t, ht, d, ψ, hψ, hψk, hψX⟩ := AdaptedDerivativeNeighborhood.Construction.derivativeNeighborhood_exists_adapted_coordinates D z Q.asIdeal
  let S := Localization.Away t
  let f : R →ₐ[k] S := (IsScalarTower.toAlgHom k A S).comp (IsScalarTower.toAlgHom k R A)
  have hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      IsOpenImmersion.of_isLocalization (D z)
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsOpenImmersion.of_isLocalization t
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (algebraMap A S)))
    rw [Spec.map_comp]
    infer_instance
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hopen
  have het : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) := inferInstance
  have hf : f.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  have hdim : ringKrullDim S ≤ 2 := (Affine.OpenDimension.Construction.ringKrullDim_le_of_spec_openImmersion f.toRingHom).trans hd
  have hzmap := Ideal.mem_map_of_mem f.toRingHom hz
  rw [Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J n] at hzmap
  have hfx : f z = algebraMap R S z := (IsScalarTower.algebraMap_apply R A S z).symm
  have hzcoord : ψ (MvPolynomial.X (Sum.inr ())) ∈
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
    rw [hψX, ← hfx]
    exact hzmap
  obtain ⟨T⟩ := Coordinate.SurfaceOrderTree.Construction.exists_surface_order_tree_of_coordinate_map k (.of S) ψ hψ hψk
    hdim (J.map f.toRingHom) n (Sum.inr ()) hzcoord
  let C : SurfaceOrderOpenChart k R J (n + 1) := ⟨.of S, inferInstance, f, hopen, T⟩
  obtain ⟨P, hP⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime t Q ht
  refine ⟨C, ?_⟩
  change q ∈ Set.range (PrimeSpectrum.comap f.toRingHom)
  refine ⟨P, PrimeSpectrum.ext ?_⟩
  have hPI : P.asIdeal.comap (algebraMap A S) = Q.asIdeal := congrArg PrimeSpectrum.asIdeal hP
  have hQI : Q.asIdeal.comap (algebraMap R A) = q.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
  change P.asIdeal.comap ((algebraMap A S).comp (algebraMap R A)) = q.asIdeal
  rw [← Ideal.comap_comap, hPI, hQI]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.OrderOpenChart.Construction
