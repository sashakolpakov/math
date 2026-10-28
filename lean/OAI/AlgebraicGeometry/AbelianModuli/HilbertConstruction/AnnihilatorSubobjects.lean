import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.Annihilator
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType

/-! # Annihilator Subobjects -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AnnihilatorSubobjects

noncomputable section

/-! Annihilators pass to actual subobjects. The ideal of a closed immersion
annihilates every coherent module pushed forward from it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem coherentAnnihilator_le_of_mono
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ N) [ha : Mono a] : Coherent.Annihilator.coherentAnnihilator N ≤ Coherent.Annihilator.coherentAnnihilator M := by
  intro U r hr
  change r ∈ Module.annihilator Γ(X, U.1) Γ(N, U.1) at hr
  change r ∈ Module.annihilator Γ(X, U.1) Γ(M, U.1)
  apply Module.mem_annihilator.mpr
  intro m
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U.1) :=
    SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  have : Limits.PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op U.1)
  have hmono : Mono (F.map a) := @Functor.map_mono _ _ _ _ F _ N M a ha
  apply (ModuleCat.mono_iff_injective (F.map a)).mp hmono
  exact ((F.map a).hom.map_smul r m).trans
    ((Module.mem_annihilator.mp hr ((F.map a).hom m)).trans ((F.map a).hom.map_zero).symm)

theorem closedIdeal_annihilates_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (N : X.Modules) [N.IsQuasicoherent] [N.IsFiniteType] :
    letI := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f N
    letI := HilbertConstruction.Finite.ImageType.finite_directImage_finiteType f N
    f.ker ≤ Coherent.Annihilator.coherentAnnihilator ((pushforward f).obj N) := by
  let := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f N
  let := HilbertConstruction.Finite.ImageType.finite_directImage_finiteType f N
  intro U r hr
  rw [Scheme.Hom.ker_apply] at hr
  change r ∈ Module.annihilator Γ(Y, U.1) Γ((pushforward f).obj N, U.1)
  apply Module.mem_annihilator.mpr
  intro m
  change f.app U.1 r • (show Γ(N, f ⁻¹ᵁ U.1) from m) = 0
  rw [show f.app U.1 r = 0 from hr, zero_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AnnihilatorSubobjects
