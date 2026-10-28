import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.TwistVanishing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmpleSectionEmbedding
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicProjectivePowers

/-! # Ample Power Vanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmplePowerVanishing

noncomputable section

/-! An actual ample line bundle on a proper scheme has a positive
power whose successive tensor powers satisfy Serre vanishing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry MonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra
local instance (X : Scheme.{0}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem ample_tensorPowers_vanishing_step
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ∀ (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType],
      ∃ b : ℕ, ∀ m : ℕ, b ≤ m → ∀ q : ℕ, 0 < q →
        Subsingleton (SheafCohomology.AffineH.Projective.H (M ⊗ (L.tensorPower (m * d)).sheaf) q) := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨d, hd, P, hP, n, s, hs, he⟩ := AmpleSectionEmbedding.PolarizationEmbedding.exists_closed_section_embedding L f hL
  let a := AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs
  let p : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).left :=
    pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ
  have hp : (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ p = a := pullback.lift_fst _ _ _
  have : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left := he
  have : IsIso p := inferInstanceAs
    (IsIso (pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom S.toSpecΓ))
  have : IsClosedImmersion a := hp ▸
    (inferInstance : IsClosedImmersion ((AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ p))
  obtain ⟨eP⟩ := hP.unique (L.tensorPower_isTensorPower d)
  refine ⟨d, hd, fun M _ _ => ?_⟩
  obtain ⟨b, hb⟩ := Projective.TwistVanishing.projectiveTwist_eventually_vanishing a (0 : Fin (n + 1)) M
  refine ⟨b, fun m hm q hq => ?_⟩
  obtain ⟨eH⟩ := IntrinsicProjectivePowers.PolarizationEmbedding.nativeHyperplane_section_pullback P f s hs (0 : Fin (n + 1)) m
  let eT := eH ≪≫ (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerFunctor X m).mapIso eP ≪≫
    (L.tensorPowerComposeIso m d).symm
  have : Subsingleton (SheafCohomology.AffineH.Projective.H (M ⊗ (Scheme.Modules.pullback a).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := Γ(S, ⊤)) (0 : Fin (n + 1)) m)) q) :=
    hb m hm q hq
  let e := Iso.refl M ⊗ᵢ eT
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor X q).map e.inv)).injective.subsingleton

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AmplePowerVanishing
