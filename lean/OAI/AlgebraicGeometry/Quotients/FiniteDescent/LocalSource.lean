import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineBasis
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeTrivializationBasis

/-! # Local Source -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalSource.Construction.LocalSourceBasis

/-!
# Relation source bases from local bases on the original base

The relation source is a base change of the subgroup. A basis over an affine
base neighborhood supplies a basis on every affine object chart lying above
that neighborhood, even when the ambient object scheme is not affine.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem exists_basis_over_open
    {H S R X : Scheme.{u}} (h : H ⟶ S) (a : X ⟶ S) (r : R ⟶ H) (s : R ⟶ X)
    (hs : IsPullback r s h a) [IsFinite h]
    (B : S.Opens) [IsAffine B] (D : X.Opens) [IsAffine D] (hD : D ≤ a ⁻¹ᵁ B)
    {ι : Type v}
    (b : letI := (h ∣_ B).appTop.hom.toAlgebra;
      Module.Basis ι Γ(B.toScheme, ⊤) Γ((h ⁻¹ᵁ B).toScheme, ⊤)) :
    letI := (s ∣_ D).appTop.hom.toAlgebra
    Nonempty (Module.Basis ι Γ(D.toScheme, ⊤) Γ((s ⁻¹ᵁ D).toScheme, ⊤)) := by
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  have : IsAffine (h ⁻¹ᵁ B).toScheme := isAffine_of_isAffineHom (h ∣_ B)
  have : IsAffine (s ⁻¹ᵁ D).toScheme := isAffine_of_isAffineHom (s ∣_ D)
  have hR : s ⁻¹ᵁ D ≤ r ⁻¹ᵁ (h ⁻¹ᵁ B) := by
    intro z hz
    have he : h (r z) = a (s z) := congrArg (fun f => f z) hs.w
    change h (r z) ∈ B
    rw [he]
    exact hD hz
  let aD : D.toScheme ⟶ B.toScheme := a.resLE B D hD
  let rD : (s ⁻¹ᵁ D).toScheme ⟶ (h ⁻¹ᵁ B).toScheme :=
    r.resLE (h ⁻¹ᵁ B) (s ⁻¹ᵁ D) hR
  have hp : IsPullback rD (s ∣_ D) (h ∣_ B) aD := by
    apply IsPullback.of_right (t := (isPullback_morphismRestrict h B).flip)
    · simpa only [aD, rD, Scheme.Hom.resLE_comp_ι] using
        (isPullback_morphismRestrict s D).flip.paste_horiz hs
    · apply (cancel_mono B.ι).mp
      dsimp only [aD, rD]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
        Scheme.Hom.resLE_comp_ι_assoc, hs.w, morphismRestrict_ι_assoc]
  exact AffineBasis.Construction.AffineBasisTransfer.of_isPullback (h ∣_ B) aD rD (s ∣_ D) hp b

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalSource.Construction.LocalSourceBasis
