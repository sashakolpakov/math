import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoherentCohomology
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseZeroSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.BaseGlobalRestriction

/-! # Global Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.GlobalSections

noncomputable section

/-! The actual global sections of a coherent module on a proper scheme
are finite over the original affine base's section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem proper_coherent_globalSections_finite
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
    Module.Finite Γ(S, ⊤) Γ(M, ⊤) := by
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M 0
  let := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
  have := CoherentCohomology.proper_coherent_cohomologyFinite_affine f M 0
  exact Module.Finite.equiv (SheafCohomology.Projective.BaseZeroSections.baseHZeroLinearEquivGlobalSections f M)

theorem proper_coherent_baseModuleTop_finite
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite Γ(S, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (.op ⊤)) := by
  let := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
  have := proper_coherent_globalSections_finite f M
  apply Module.Finite.of_surjective (SheafCohomology.Projective.BaseGlobalRestriction.baseGlobalRestriction f M ⊤)
  intro s
  refine ⟨s, ?_⟩
  change M.presheaf.map (𝟙 (.op ⊤)) s = s
  rw [M.presheaf.map_id]
  rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.GlobalSections
