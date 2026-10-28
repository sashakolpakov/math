import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffineDetection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantAffineHas

/-! # Invariant Affine -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InvariantAffine.Construction

noncomputable section

/-! An invariant affine open descends to an affine open in the actual
finite-flat quotient. The relation's basis is transported from its
finite-free source scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem invariantAffineOpen_descends
    {H S R X Y : Scheme.{u}} [IsAffine H] [IsAffine S]
    (q : X ⟶ Y) [Flat q] [Surjective q] [QuasiCompact q]
    (s t : R ⟶ X) (hk : IsKernelPair q s t)
    (h : H ⟶ S) [IsFinite h] (a : X ⟶ S) (r : R ⟶ H)
    (hs : IsPullback r s h a) {ι : Type v} [Fintype ι]
    (b : letI := h.appTop.hom.toAlgebra; Module.Basis ι Γ(S, ⊤) Γ(H, ⊤))
    (W : X.Opens) (hW : IsAffineOpen W) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    IsAffineOpen (Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens.descend q hk W hinv) := by
  have : IsAffine W := hW
  have : IsFinite s := MorphismProperty.of_isPullback hs inferInstance
  have : IsAffine (s ⁻¹ᵁ W).toScheme := isAffine_of_isAffineHom (s ∣_ W)
  obtain ⟨bW⟩ := Quotients.FiniteDescent.InvariantAffineHas.Construction.InvariantAffineBasis.exists_basis_restrict h a r s hs b W
  exact AffineDetection.Construction.affine_of_finiteFree_kernelPair
    (Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens.restrictProjection q hk W hinv) (s ∣_ W)
    ((R.isoOfEq hinv).hom ≫ t ∣_ W)
    (Quotients.FiniteDescent.InvariantOpensEq.Construction.InvariantOpens.restrictProjection_isKernelPair q hk W hinv) bW

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InvariantAffine.Construction
