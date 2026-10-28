import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAffineSectionRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAlgebraLocalBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationPushoutBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RestrictionRingPushout
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Flat Affine Local Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAffineLocalFrame

noncomputable section

/-! A finite flat map of constant rank over a locally Noetherian scheme has actual finite bases on arbitrarily small affine neighborhoods. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem finiteFlat_exists_affineLocalBasis {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] {n : ℕ} (hn : ∀ x, f.finrank x = n)
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
      Nonempty (@Module.Basis (Fin n) Γ(X, V) Γ(Y, f ⁻¹ᵁ V) _ _ (f.app V).hom.toModule) := by
  let R := Γ(X, U)
  let A := Γ(Y, f ⁻¹ᵁ U)
  let : Algebra R A := (f.app U).hom.toAlgebra
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite R A := f.finite_app U hU
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  have hY : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have : Module.Flat R A := by
    have hf := f.flat_appLE hU hY (le_refl (f ⁻¹ᵁ U))
    rw [Scheme.Hom.appLE_eq_app] at hf
    exact hf
  let p := hU.primeIdealOf ⟨x, hx⟩
  have hr : Module.rankAtStalk A p = n := by
    change (f.app U).hom.finrank p = n
    rw [FlatAffineSectionRank.finiteFlat_affineSection_rank f hU p]
    exact hn _
  obtain ⟨a, ha, ⟨b⟩⟩ := FlatAlgebraLocalBasis.finiteFlat_exists_localModuleBasis (R := R) A p hr
  let V := X.basicOpen a
  have hV : IsAffineOpen V := hU.basicOpen a
  have hVU : V ≤ U := X.basicOpen_le a
  have hxV : x ∈ V := by
    have hp : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a := by
      rw [hU.fromSpec_preimage_basicOpen a]
      exact ha
    change hU.fromSpec p ∈ V at hp
    simpa only [p, hU.fromSpec_primeIdealOf] using hp
  refine ⟨V, hxV, hVU, hV, ⟨?_⟩⟩
  exact LocalizationPushoutBasis.localizationPushoutBasis (f.app U).hom (X.presheaf.map (homOfLE hVU).op).hom
    (Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hv => hVU hv)).op).hom
    (f.app V).hom (Affine.RestrictionRingPushout.affineRestriction_isPushout f hVU hU hV hY).flip
    (Submonoid.powers a) (hU.isLocalization_basicOpen a) b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAffineLocalFrame
