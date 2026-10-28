import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenPrincipalIdealModule

/-! # Ideal Bundle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle.Cycles

noncomputable section

/-! An actual scheme morphism with locally regular principal image
ideals has a genuine invertible ideal sheaf. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X)

def HasRegularPrincipalImageIdeals : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ t : Γ(X, U.1),
    IsRegular t ∧ RingHom.ker (f.app U.1).hom = Ideal.span {t}

def cartierIdealLineBundle [QuasiCompact f] (h : HasRegularPrincipalImageIdeals f) : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X where
  sheaf := LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule f
  locallyTrivial x := by
    obtain ⟨U, hxU, t, ht, hker⟩ := h x
    exact ⟨U.1, hxU, ⟨Affine.OpenPrincipalIdealModule.BundleCycles.affineOpenPrincipalIdealModuleIso f U t hker ht⟩⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealBundle.Cycles
