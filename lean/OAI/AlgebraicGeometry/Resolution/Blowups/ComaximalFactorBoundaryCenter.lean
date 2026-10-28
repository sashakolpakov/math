import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterEtaleBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CanonicalBoundaryAtlas

/-! # Comaximal Factor Boundary Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A disjoint factor of a boundary-compatible center retains common boundary coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.comaximalFactor
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    (I K L : Ideal R) {ι : Type v} {w : ι → R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (hI : I = K * L) (hdisjoint : K ⊔ L = ⊤) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R K w F := by
  intro p hp
  have hex : ∃ g ∈ L, g ∉ p.asIdeal := by
    by_contra! hL
    have hle : K ⊔ L ≤ p.asIdeal := sup_le hp hL
    rw [hdisjoint] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨g, hgL, hgp⟩ := hex
  let S := Localization.Away g
  let φ : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  have hφ : φ.toRingHom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway g)
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := IsOpenImmersion.of_isLocalization g
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime g p hgp
  have hL : L.map φ.toRingHom = ⊤ := Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem φ.toRingHom hgL) (IsLocalization.Away.algebraMap_isUnit g)
  have he : I.map φ.toRingHom = K.map φ.toRingHom := by rw [hI, Ideal.map_mul, hL, Ideal.mul_top]
  have hc := h.etale_baseChange (S := .of S) φ hφ
  rw [he] at hc
  have hKq : K.map φ.toRingHom ≤ q.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    have heq := congrArg PrimeSpectrum.asIdeal hq
    change q.asIdeal.comap φ.toRingHom = p.asIdeal at heq
    rw [heq]
    exact hp
  obtain ⟨C⟩ := hc q hKq
  exact ⟨C.comp (S := .of S) K w F φ p hq⟩

def Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.comaximalFactor
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {I : X.IdealSheafData}
    {β : Type} {D : β → X.IdealSheafData} (A : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D)
    (K L : X.IdealSheafData) (hI : I = K * L) (hdisjoint : K ⊔ L = ⊤) :
    Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f K D where
  indices := A.indices
  opens := A.opens
  cover := A.cover
  equations := A.equations
  component := A.component
  divided := A.divided
  contained i j hj := by
    have hmem := A.contained i j hj
    have he := congrArg (fun J : X.IdealSheafData => J.ideal (A.opens i)) hI
    rw [he] at hmem
    exact Ideal.mul_le_left hmem
  boundary := A.boundary
  center i := by
    let : Algebra ℂ Γ(X, A.opens i) := Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f (A.opens i)
    exact (A.center i).comaximalFactor (I.ideal (A.opens i)) (K.ideal (A.opens i)) (L.ideal (A.opens i))
      (congrArg (fun J : X.IdealSheafData => J.ideal (A.opens i)) hI)
      (congrArg (fun J : X.IdealSheafData => J.ideal (A.opens i)) hdisjoint)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
