import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalRadial
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayFixedRadialExpansion
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AuxiliaryCoordinate

/-! # Spherical Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates

noncomputable section

section

/-! Transport actual GeometricTheta spherical inputs to the fixed native finite
coordinates. The local inverse-transpose action becomes ordinary radial
invariance, and the original away subgroup is conjugated exactly. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

namespace Local

theorem finite_action_conjugate {I MpR MpF MpA : Type*} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA] (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u m : MpF) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    D.finite.action (u * m * u⁻¹) (D.finite.action u f) =
      D.finite.action u (D.finite.action m f) := by
  rw [← LinearEquiv.mul_apply, ← map_mul]
  rw [mul_assoc u m u⁻¹, mul_assoc u (m * u⁻¹) u, mul_assoc m u⁻¹ u,
    inv_mul_cancel, mul_one, map_mul, LinearEquiv.mul_apply]

theorem finite_action_inverse_cancel {I MpR MpF MpA : Type*} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA] (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u : MpF) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) : D.finite.action u⁻¹ (D.finite.action u f) = f := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem finite_action_conjugate_inverse {I MpR MpF MpA : Type*} [Fintype I] [DecidableEq I]
    [Group MpR] [Group MpF] [Group MpA] (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData I MpR MpF MpA)
    (u m : MpF) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    D.finite.action m (D.finite.action u⁻¹ f) =
      D.finite.action u⁻¹ (D.finite.action (u * m * u⁻¹) f) := by
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, finite_action_inverse_cancel]

end Local

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)

theorem native_spherical_coordinate_active
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (f : D.sphericalInputs) :
    D.weil.finite.action u f.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q)
      (ActiveLocalHecke.activeFiniteRepresentation q c D.pel.reference.distinguished D.weil) := by
  have hs := SphericalRadial.native_local_splitting_eq_dual D c u hp
  have hs' (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) : D.splitting (g, 1) =
      CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u g := DFunLike.congr_fun hs g
  intro g hg
  have hf := f.property (Contragredient.Local.contragredient ℚ_[q] g, 1)
    ⟨(Contragredient.Local.contragredient_integral_iff q g).mpr hg, D.awayLevel.one_mem⟩
  change D.weil.finite.action (D.splitting (Contragredient.Local.contragredient ℚ_[q] g, 1)) f.val = f.val at hf
  rw [hs'] at hf
  change D.weil.finite.action
    (CoordinateLocalHecke.coordinateActiveLift q c D.pel.reference.distinguished D.weil u
      (Contragredient.Local.contragredient ℚ_[q] (Contragredient.Local.contragredient ℚ_[q] g))) f.val = f.val at hf
  rw [Contragredient.Local.contragredient_involutive] at hf
  have hc := CoordinateLocalHecke.coordinateActive_action q c D.pel.reference.distinguished D.weil u g
    (D.weil.finite.action u f.val)
  rw [Local.finite_action_inverse_cancel] at hc
  change D.weil.finite.action (CoordinateLocalHecke.coordinateActiveLift q c D.pel.reference.distinguished D.weil u g) f.val =
    D.weil.finite.action u⁻¹
      (ActiveLocalHecke.activeFiniteRepresentation q c D.pel.reference.distinguished D.weil g (D.weil.finite.action u f.val)) at hc
  rw [hf] at hc
  apply (D.weil.finite.action u⁻¹).injective
  exact hc.symm.trans (Local.finite_action_inverse_cancel D.weil u f.val).symm

def nativeConjugatedAwayLevel : Subgroup MpF :=
  D.awayLevel.toSubgroup.map
    ((MulAut.conj u).toMonoidHom.comp (D.splitting.comp (MonoidHom.inr (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga)))

theorem native_spherical_coordinate_away (f : D.sphericalInputs) :
    D.weil.finite.action u f.val ∈ RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (nativeConjugatedAwayLevel D u)
      D.weil.finite.action := by
  rintro m ⟨g, hg, rfl⟩
  change D.weil.finite.action (u * D.splitting (1, g) * u⁻¹) (D.weil.finite.action u f.val) = _
  rw [Local.finite_action_conjugate]
  have hf := f.property (1, g) ⟨(RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).one_mem, hg⟩
  change D.weil.finite.action (D.splitting (1, g)) f.val = f.val at hf
  rw [hf]

end

/-! Every actual native spherical input has a finite expansion in radial
families, each lying at the same full active-and-away level. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [DecidableEq (Fin s)] [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q (Fin s × Fin 3) Ga MpR MpF MpA)
  {n : ℕ} (c : (Fin s × Fin 3) ≃ Fin n) (u : MpF)

theorem native_auxiliaryCoordinate_fixed
    (hs : D.splitting.comp (MonoidHom.inl (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) Ga) =
      CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u)
    (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
    (hφ : ∀ b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q, AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q D.pel.reference.distinguished φ b ∈
      RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.fixedInputs (nativeConjugatedAwayLevel D u) D.weil.finite.action)
    (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ b ∈ D.sphericalInputs := by
  apply (RepresentationTheory.Theta.Geometric.Away.Spherical.fixedProduct_iff (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q) D.awayLevel.toSubgroup D.finiteWeil _).mpr
  constructor
  · intro g hg
    have he : D.splitting (g, 1) = CoordinateDualHecke.Local.coordinateDualLift q c D.pel.reference.distinguished D.weil u g :=
      DFunLike.congr_fun hs g
    change D.weil.finite.action (D.splitting (g, 1)) _ = _
    rw [he]
    exact AuxiliaryCoordinate.Local.auxiliaryCoordinate_active_fixed q D.pel.reference.distinguished D.weil u φ c b
      (Contragredient.Local.contragredient ℚ_[q] g) ((Contragredient.Local.contragredient_integral_iff q g).mpr hg)
  · intro g hg
    change D.weil.finite.action (D.splitting (1, g))
      (D.weil.finite.action u⁻¹ (AuxiliaryRadialHecke.Local.auxiliaryFiniteRadialEmbedding q D.pel.reference.distinguished φ b)) = _
    rw [Local.finite_action_conjugate_inverse]
    have hm : u * D.splitting (1, g) * u⁻¹ ∈ nativeConjugatedAwayLevel D u := ⟨g, hg, rfl⟩
    rw [hφ b _ hm]
    rfl

theorem native_spherical_radial_expansion
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (haway : ∀ g ∈ D.awayLevel, ∀ p t : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.weil.finite.project (u * D.splitting (1, g) * u⁻¹)).val.mulVec
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t))
    (f : D.sphericalInputs) :
    ∃ (a : ℤ →₀ RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
      (J : ℤ → RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs),
      (∀ k b, (J k b).val = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u (a k) b) ∧
      f = ∑ k ∈ a.support, J k (Radial.Cyclicity.ball q k) := by
  have hL : ∀ m ∈ nativeConjugatedAwayLevel D u, ∀ p t : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.weil.finite.project m).val.mulVec
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t) := by
    rintro m ⟨g, hg, rfl⟩ p t
    exact haway g hg p t
  obtain ⟨a, ha, hfix⟩ := AwayFixedRadialExpansion.Local.away_fixed_radial_coefficient_expansion q c D.pel.reference.distinguished D.weil
    (nativeConjugatedAwayLevel D u) hL (D.weil.finite.action u f.val)
    (native_spherical_coordinate_active D c u hp f) (native_spherical_coordinate_away D u f)
  let J : ℤ → RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs := fun k =>
    (AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u (a k)).codRestrict
      D.sphericalInputs (native_auxiliaryCoordinate_fixed D c u
        (SphericalRadial.native_local_splitting_eq_dual D c u hp) (a k) (hfix k))
  refine ⟨a, J, fun _ _ => rfl, ?_⟩
  apply Subtype.ext
  have he := congrArg (D.weil.finite.action u⁻¹) ha
  rw [Local.finite_action_inverse_cancel] at he
  symm
  simp only [Submodule.coe_sum]
  change (∑ k ∈ a.support,
    AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u (a k) (Radial.Cyclicity.ball q k)) = f.val
  rw [← he]
  change _ = D.weil.finite.action u⁻¹
    (RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators.Realization.finiteProductTestEquiv (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockChart q D.pel.reference.distinguished)
      (Finsupp.lsum ℂ (fun k : ℤ => RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.tensorLeftLinear (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.radialTest q (Radial.Cyclicity.ball q k))) a))
  simp only [Finsupp.lsum_apply, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (D.weil.finite.action u⁻¹)
    (RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization.finiteRadialEmbedding_tensor q _ _ _ _ (Radial.Cyclicity.ball q k))

theorem native_nonzero_spherical_radial_family
    (hp : ∀ g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q, D.weil.finite.project (D.splitting (g, 1)) =
      (D.weil.finite.project u)⁻¹ * RepresentationTheory.Hecke.RadialDilation.IndexedPrimePhaseAction.Realization.indexedPrimeSymplectic q c
        (RepresentationTheory.Weil.Local.Generators.Construction.leviSymplectic
          (ActiveBlockMatrices.Local.activeBlockGL c D.pel.reference.distinguished (Contragredient.Local.contragredient ℚ_[q] g))) *
            D.weil.finite.project u)
    (haway : ∀ g ∈ D.awayLevel, ∀ p t : RepresentationTheory.Hecke.RadialDilation.Mem.Realization.Position q,
      (D.weil.finite.project (u * D.splitting (1, g) * u⁻¹)).val.mulVec
        (Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t)) =
        Sum.elim (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished p)
          (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.finiteBlockInclusion q D.pel.reference.distinguished t))
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : D.sphericalInputs →ₗ[ℂ] W) (f : D.sphericalInputs) (hf : T f ≠ 0) :
    ∃ (φ : RepresentationTheory.Hecke.RadialDilation.TestSections.Realization.lcCompactSpace (RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart.Realization.FiniteAwayPosition q D.pel.reference.distinguished))
      (J : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] D.sphericalInputs) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q),
      φ ≠ 0 ∧
      (∀ a, (J a).val = AuxiliaryCoordinate.Local.auxiliaryCoordinateRadialEmbedding q D.pel.reference.distinguished D.weil u φ a) ∧
      T (J b) ≠ 0 := by
  obtain ⟨a, J, hJ, hsum⟩ := native_spherical_radial_expansion D c u hp haway f
  have hn : (∑ k ∈ a.support, T (J k (Radial.Cyclicity.ball q k))) ≠ 0 := by
    rw [← map_sum, ← hsum]
    exact hf
  obtain ⟨k, hk, hTk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  exact ⟨a k, J k, Radial.Cyclicity.ball q k, Finsupp.mem_support_iff.mp hk, hJ k, hTk⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SphericalCoordinates
