import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentAnnihilator
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType

/-! # Annihilator Subobjects -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorSubobjects

noncomputable section

/-! Annihilators pass to actual subobjects. The ideal of a closed immersion
annihilates every coherent module pushed forward from it. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem coherentAnnihilator_le_of_mono
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ N) [Mono a] : CoherentAnnihilator.coherentAnnihilator N ≤ CoherentAnnihilator.coherentAnnihilator M := by
  intro U r hr
  change r ∈ Module.annihilator Γ(X, U.1) Γ(N, U.1) at hr
  change r ∈ Module.annihilator Γ(X, U.1) Γ(M, U.1)
  apply Module.mem_annihilator.mpr
  intro m
  have hmono : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map a) := inferInstance
  apply (ModuleCat.mono_iff_injective (a.val.app (op U.1))).mp hmono
  rw [map_zero]
  exact ((a.val.app (op U.1)).hom.map_smul r m).trans
    (Module.mem_annihilator.mp hr (a.val.app (op U.1) m))

theorem closedIdeal_annihilates_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (N : X.Modules) [N.IsQuasicoherent] [N.IsFiniteType] :
    letI := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (M := N) f
    letI := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion (M := N) f
    f.ker ≤ CoherentAnnihilator.coherentAnnihilator ((pushforward f).obj N) := by
  let := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (M := N) f
  let := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion (M := N) f
  intro U r hr
  rw [Scheme.Hom.ker_apply] at hr
  change r ∈ Module.annihilator Γ(Y, U.1) Γ((pushforward f).obj N, U.1)
  apply Module.mem_annihilator.mpr
  intro m
  change f.app U.1 r • (show Γ(N, f ⁻¹ᵁ U.1) from m) = 0
  rw [show f.app U.1 r = 0 from hr, zero_smul]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorSubobjects
