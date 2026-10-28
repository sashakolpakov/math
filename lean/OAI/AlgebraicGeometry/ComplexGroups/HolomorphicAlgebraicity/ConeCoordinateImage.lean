import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.InjectiveAnalyticImage
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeNormalization

/-! # Cone Coordinate Image -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCoordinateImage.Constructions.Cone

noncomputable section

section

/-!
# Analytic images under a prescribed finite cone projection

A complex linear map whose kernel meets a closed analytic cone only at zero
has an image that is locally analytic away from zero. The proof removes
kernel directions one at a time, retaining the prescribed map.
-/

open Set

theorem holomorphicZeroSetAt_prescribed_linear_image_coordinates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (n : ℕ) : ∀ {S : Set (Fin n → ℂ)}, IsClosed S →
      (∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S) →
      (∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v) →
      ∀ L : (Fin n → ℂ) →L[ℂ] F,
      (∀ v ∈ S, L v = 0 → v = 0) →
      ∀ y : F, y ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  classical
  induction n with
  | zero =>
    intro S hS _ hlocal L _ y hy
    exact InjectiveAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_injective_linear_image hS hlocal L
      (fun _ _ _ => Subsingleton.elim _ _) y hy
  | succ n ih =>
    intro S hS hcone hlocal L hker y hy
    by_cases hL : Function.Injective L
    · exact InjectiveAnalyticImage.Constructions.Cone.holomorphicZeroSetAt_injective_linear_image hS hlocal L hL y hy
    obtain ⟨u, v, huv, hne⟩ := Function.not_injective_iff.mp hL
    have hv0 : u - v ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    change (u - v) i ≠ 0 at hi
    let w := ((u - v) i)⁻¹ • (u - v)
    have hw : w i = 1 := by
      change ((u - v) i)⁻¹ * (u - v) i = 1
      exact inv_mul_cancel₀ hi
    have hLw : L w = 0 := by simp [w, map_sub, huv]
    have hwS : w ∉ S := by
      intro h
      have hz := congrFun (hker w h hLw) i
      exact one_ne_zero (hw.symm.trans hz)
    let b := ConeNormalization.Constructions.Cone.omittedCoordinateEquiv i
    let e := LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv i w
    let Q := b.toContinuousLinearMap.comp (SegreProjection.Constructions.Segre.projectionAlong i w)
    let T := Q '' S
    let R := e.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℂ _ ℂ).comp b.symm.toContinuousLinearMap)
    let L' := L.comp R
    have hsection (a : Fin (n + 1) → ℂ) :
        e.symm (SegreProjection.Constructions.Segre.projectionAlong i w a, 0) = a - a i • w := by
      ext j
      by_cases hj : j = i
      · simp [e, LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv, hj, hw]
      · simp [e, LinearAnalyticImage.Constructions.Segre.projectionAlongEquiv, SegreProjection.Constructions.Segre.projectionAlong, hj]
    have hfactor (a : Fin (n + 1) → ℂ) : L' (Q a) = L a := by
      change L (e.symm (b.symm (b (SegreProjection.Constructions.Segre.projectionAlong i w a)), 0)) = L a
      rw [b.symm_apply_apply, hsection, map_sub, map_smul, hLw, smul_zero, sub_zero]
    have hproper : IsProperMap (fun a : S => Q a) :=
      b.toHomeomorph.isProperMap.comp (SegreProjection.Constructions.Segre.isProperMap_projectionAlong hS hcone i w hw hwS)
    have hclosedT : IsClosed T := by
      change IsClosed (Q '' S)
      rw [image_eq_range]
      exact hproper.isClosedMap.isClosed_range
    have hconeT : ∀ (c : ℂ) ⦃a⦄, a ∈ T → c • a ∈ T := by
      intro c a ha
      obtain ⟨a, ha, rfl⟩ := ha
      exact ⟨c • a, hcone c ha, map_smul Q c a⟩
    have hlocalT : ∀ a ∈ T, a ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T a := by
      intro a _ ha
      have hba : b.symm a ≠ 0 := by
        intro hz
        exact ha (by simpa only [b.apply_symm_apply, map_zero] using congrArg b hz)
      have h := (LinearAnalyticImage.Constructions.Segre.holomorphicZeroSetAt_projectionAlong hS hcone i w hw hwS hlocal
        (b.symm a) hba).image_equiv b
      simpa only [T, Q, Set.image_image, b.apply_symm_apply, Function.comp_def,
        ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe] using h
    have hkerT : ∀ a ∈ T, L' a = 0 → a = 0 := by
      intro a ha hLa
      obtain ⟨v, hv, rfl⟩ := ha
      have hv0 := hker v hv (by rwa [hfactor] at hLa)
      rw [hv0, map_zero]
    have himage : L' '' T = L '' S := by
      change L' '' (Q '' S) = L '' S
      rw [image_image]
      congr 1
      funext a
      exact hfactor a
    rw [← himage]
    exact ih hclosedT hconeT hlocalT L' hkerT y hy

theorem holomorphicZeroSetAt_prescribed_linear_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set E} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (L : E →L[ℂ] F) (hker : ∀ v ∈ S, L v = 0 → v = 0)
    (y : F) (hy : y ≠ 0) : ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (L '' S) y := by
  let e := (Module.finBasis ℂ E).equivFunL
  let T := e '' S
  let L' := L.comp e.symm.toContinuousLinearMap
  have hclosedT : IsClosed T := e.toHomeomorph.isClosedMap S hS
  have hconeT : ∀ (c : ℂ) ⦃v⦄, v ∈ T → c • v ∈ T := by
    intro c v hv
    obtain ⟨v, hv, rfl⟩ := hv
    exact ⟨c • v, hcone c hv, map_smul e c v⟩
  have hlocalT : ∀ v ∈ T, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T v := by
    intro v hv hv0
    obtain ⟨v, hv, rfl⟩ := hv
    exact (hlocal v hv (fun h => hv0 (by simp [h]))).image_equiv e
  have hkerT : ∀ v ∈ T, L' v = 0 → v = 0 := by
    intro v hv hLv
    obtain ⟨v, hv, rfl⟩ := hv
    have hz : v = 0 := hker v hv (by simpa only [L', ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply] using hLv)
    rw [hz, map_zero]
  have h := holomorphicZeroSetAt_prescribed_linear_image_coordinates
    (Module.finrank ℂ E) hclosedT hconeT hlocalT L' hkerT y hy
  have heq : L' '' T = L '' S := by
    simp only [T, L', image_image, ContinuousLinearMap.coe_comp, Function.comp_def,
      ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
  rwa [heq] at h

end

/-!
# Adding a scalar coordinate to a fixed cone normalization

The image of a cone under a normalization and one additional linear
functional is closed, radial, and analytic away from zero. Its projection
onto the normalization coordinates is proper and has finite fibers.
-/

open Set

theorem coordinate_image_properties
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {S : Set E} (hS : IsClosed S)
    (hcone : ∀ (c : ℂ) ⦃v⦄, v ∈ S → c • v ∈ S)
    (hlocal : ∀ v ∈ S, v ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S v)
    (L : E →L[ℂ] F) (hker : ∀ v ∈ S, L v = 0 → v = 0)
    (hfinite : ∀ y : F, {v | v ∈ S ∧ L v = y}.Finite)
    (ℓ : E →L[ℂ] ℂ) :
    let T := (L.prod ℓ) '' S
    IsClosed T ∧
    (∀ (c : ℂ) ⦃p⦄, p ∈ T → c • p ∈ T) ∧
    (∀ p, p ≠ 0 → ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt T p) ∧
    IsProperMap (fun p : T => p.val.1) ∧
    (∀ y : F, {z : ℂ | (y, z) ∈ T}.Finite) ∧
    ∀ p ∈ T, p.1 = 0 → p = 0 := by
  let Q := L.prod ℓ
  let T := Q '' S
  have hkerQ : ∀ v ∈ S, Q v = 0 → v = 0 := by
    intro v hv hQv
    exact hker v hv (congrArg Prod.fst hQv)
  have hproperQ := Projection.Constructions.Cone.isProperMap_projection hS hcone Q hkerQ
  have hclosedT : IsClosed T := by
    rw [show T = Q '' S from rfl, image_eq_range]
    exact hproperQ.isClosedMap.isClosed_range
  have hconeT : ∀ (c : ℂ) ⦃p⦄, p ∈ T → c • p ∈ T := by
    intro c p hp
    obtain ⟨v, hv, rfl⟩ := hp
    exact ⟨c • v, hcone c hv, map_smul Q c v⟩
  have hkerT : ∀ p ∈ T, p.1 = 0 → p = 0 := by
    intro p hp hp0
    obtain ⟨v, hv, rfl⟩ := hp
    have hv0 := hker v hv hp0
    rw [hv0, map_zero]
  refine ⟨hclosedT, hconeT,
    holomorphicZeroSetAt_prescribed_linear_image hS hcone hlocal Q hkerQ,
    Projection.Constructions.Cone.isProperMap_projection hclosedT hconeT (ContinuousLinearMap.fst ℂ F ℂ) hkerT,
    ?_, hkerT⟩
  intro y
  apply ((hfinite y).image ℓ).subset
  intro z hz
  obtain ⟨v, hv, hvz⟩ := hz
  exact ⟨v, ⟨hv, congrArg Prod.fst hvz⟩, congrArg Prod.snd hvz⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCoordinateImage.Constructions.Cone
