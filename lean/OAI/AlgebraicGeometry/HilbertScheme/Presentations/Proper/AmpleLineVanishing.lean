import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmpleAllPowersVanishing

/-! # Ample Line Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmpleLineVanishing

noncomputable section

/-! All positive cohomology groups of sufficiently high ample powers
vanish on a proper scheme over a noetherian affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

namespace Cohomology

universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem ample_lineBundle_eventually_vanishing
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (hL : L.IsAmple) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (SheafCohomology.AffineH.Projective.H (L.tensorPower n).sheaf q) := by
  let O := AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X
  have : O.IsQuasicoherent := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.quasicoherent (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  have : O.IsFinitePresentation := Quotients.FiniteDescent.LineBundleFree.Construction.LineBundleCoherence.finitePresentation (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial X)
  have : O.IsFiniteType := by
    obtain ⟨p, hp⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData O
    refine { exists_localGeneratorsData := ⟨p.localGeneratorsData, ?_⟩ }
    constructor
    intro i
    exact (hp.isFinite_presentation i).isFiniteType_generators
  obtain ⟨b, hb⟩ := AmpleAllPowersVanishing.Cohomology.ample_tensorPowers_eventually_vanishing f L hL O
  refine ⟨b, fun n hn q hq => ?_⟩
  have : Subsingleton (SheafCohomology.AffineH.Projective.H (O ⊗ (L.tensorPower n).sheaf) q) := hb n hn q hq
  let e : O ⊗ (L.tensorPower n).sheaf ≅ (L.tensorPower n).sheaf :=
    ((SheafCohomology.Projective.TensorSections.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl _) ≪≫ λ_ _
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor X q).map e.inv)).injective.subsingleton

end Cohomology

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AmpleLineVanishing
