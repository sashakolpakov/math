import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalizedBasisAlgebra
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis

/-! # Scheme Trivialization Basis -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeTrivializationBasis.Construction.SchemeTrivialization

/-!
# Affine neighborhoods trivializing a finite locally free morphism

Local freeness of the coordinate module is converted to an actual affine
open of the base with a finite basis on the restricted morphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_affine_basis_neighborhood
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (x : S) :
    ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ n : ℕ,
      letI := (f ∣_ U).appTop.hom.toAlgebra
      Nonempty (Module.Basis (Fin n) Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤)) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := f.appTop.hom.toAlgebra
  let p : PrimeSpectrum Γ(S, ⊤) := S.isoSpec.hom x
  obtain ⟨r, hr, n, ⟨b⟩⟩ := SourceTrivializationTop.Construction.SourceTrivialization.affine_morphism_exists_basis_away f p
  let U := S.basicOpen r
  let V := f ⁻¹ᵁ U
  let : Algebra Γ(U.toScheme, ⊤) Γ(V.toScheme, ⊤) := (f ∣_ U).appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(V.toScheme, ⊤) :=
    (V.ι.appTop.hom.comp f.appTop.hom).toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(V.toScheme, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(S, ⊤) Γ(U.toScheme, ⊤) Γ(V.toScheme, ⊤) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    change V.ι.appTop (f.appTop c) = (f ∣_ U).appTop (U.ι.appTop c)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
      congrArg (fun g : V.toScheme ⟶ S => g.appTop c) (morphismRestrict_ι f U).symm
  have : IsLocalization.Away (algebraMap Γ(S, ⊤) Γ(X, ⊤) r) Γ(V.toScheme, ⊤) := by
    change IsLocalization.Away (f.appTop r) Γ((f ⁻¹ᵁ S.basicOpen r).toScheme, ⊤)
    rw [Scheme.preimage_basicOpen_top]
    infer_instance
  refine ⟨U, (isAffineOpen_top S).basicOpen r, ?_, n, ?_⟩
  · change x ∈ S.basicOpen r
    rw [← S.map_PrimeSpectrum_basicOpen_of_affine]
    exact hr
  · exact ⟨LocalizedBasisAlgebra.Construction.LocalizedBasis.algebraBasis (R := Γ(S, ⊤)) (A := Γ(X, ⊤))
      (R₁ := Γ(U.toScheme, ⊤)) (A₁ := Γ(V.toScheme, ⊤)) r b⟩

/-- The affine neighborhood and its finite basis exist over an arbitrary
base scheme, by restricting to an affine chart and transporting the result. -/
theorem exists_basis_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (x : S) :
    ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∃ n : ℕ,
      letI := (f ∣_ U).appTop.hom.toAlgebra
      Nonempty (Module.Basis (Fin n) Γ(U.toScheme, ⊤) Γ((f ⁻¹ᵁ U).toScheme, ⊤)) := by
  obtain ⟨U₀, hU₀, hxU₀, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    S.isBasis_affineOpens (show x ∈ (⊤ : S.Opens) from trivial)
  let U : S.Opens := U₀
  have hU : IsAffineOpen U := hU₀
  have hxU : x ∈ U := hxU₀
  let : IsAffine U := hU
  obtain ⟨V, hV, hxV, n, ⟨b⟩⟩ := exists_affine_basis_neighborhood (f ∣_ U) ⟨x, hxU⟩
  let : IsAffine V := hV
  let W := U.ι ''ᵁ V
  have hW : IsAffineOpen W := hV.image_of_isOpenImmersion U.ι
  let : IsAffine W := hW
  have : IsAffine ((f ∣_ U) ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom (f ∣_ U ∣_ V)
  have : IsAffine (f ⁻¹ᵁ W).toScheme := isAffine_of_isAffineHom (f ∣_ W)
  refine ⟨W, hW, ⟨⟨x, hxU⟩, hxV, rfl⟩, n, ?_⟩
  exact AffineBasis.Construction.AffineBasisTransfer.of_arrowIso (morphismRestrictRestrict f U V) b

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeTrivializationBasis.Construction.SchemeTrivialization
