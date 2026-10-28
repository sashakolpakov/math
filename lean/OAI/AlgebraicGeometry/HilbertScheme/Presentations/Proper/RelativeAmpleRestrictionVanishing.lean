import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmpleLineVanishing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullback

/-! # Relative Ample Restriction Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeAmpleRestrictionVanishing

noncomputable section

/-! Relative Serre vanishing on every actual inverse image of an
affine base open, stated for restrictions of the original tensor powers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Cohomology

universe u

theorem relativelyAmple_restrictedPowers_eventually_vanishing
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsRelativelyAmple f)
    (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H ((L.tensorPower n).sheaf.restrict (f ⁻¹ᵁ U).ι) q) := by
  have : IsAffine U.toScheme := hU
  have : IsLocallyNoetherian U.toScheme := inferInstance
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let V := f ⁻¹ᵁ U
  obtain ⟨b, hb⟩ := AmpleLineVanishing.Cohomology.ample_lineBundle_eventually_vanishing
    (f ∣_ U) (L.pullback V.ι) (hL U hU)
  refine ⟨b, fun n hn q hq => ?_⟩
  have : Subsingleton (SheafCohomology.AffineH.Projective.H ((L.pullback V.ι).tensorPower n).sheaf q) := hb n hn q hq
  let e : (L.tensorPower n).sheaf.restrict V.ι ≅ ((L.pullback V.ι).tensorPower n).sheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (L.tensorPower n).sheaf ≪≫
      Quotients.FiniteDescent.TensorPullback.Construction.TensorPullbackMap.iso V.ι L n
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor V.toScheme q).map e.hom)).injective.subsingleton

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.RelativeAmpleRestrictionVanishing
