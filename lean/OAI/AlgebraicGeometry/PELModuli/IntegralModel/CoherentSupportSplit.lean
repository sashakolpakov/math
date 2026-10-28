import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.SupportedModules
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentAnnihilator

/-! # Coherent Support Split -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentSupportSplit

noncomputable section

/-! A coherent sheaf supported on the union of two closed sets is an
extension of coherent sheaves supported on the individual closed sets. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem coherent_support_le_iff_restrict_compl_isZero
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (Z : Closeds X) :
    (CoherentAnnihilator.coherentAnnihilator M).support ≤ Z ↔
      IsZero (M.restrict (Scheme.Opens.ι (X := X) Z.compl)) := by
  rw [ModuleVanishingOpen.module_restrict_isZero_iff_le_vanishingOpen]
  constructor
  · intro h x hx
    by_contra hn
    exact hx (h ((CoherentAnnihilator.coherentAnnihilator_mem_support_iff M x).mpr hn))
  · intro h x hx
    by_contra hn
    exact (CoherentAnnihilator.coherentAnnihilator_mem_support_iff M x).mp hx (h hn)

theorem exists_coherent_support_split
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (Z Z' : Closeds X) (h : (CoherentAnnihilator.coherentAnnihilator M).support ≤ Z ⊔ Z') :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧ S.X₂ = M ∧
      ∃ (_h₁ : S.X₁.IsQuasicoherent) (_h₂ : S.X₁.IsFiniteType)
        (_h₃ : S.X₃.IsQuasicoherent) (_h₄ : S.X₃.IsFiniteType),
        (CoherentAnnihilator.coherentAnnihilator S.X₁).support ≤ Z ∧
        (CoherentAnnihilator.coherentAnnihilator S.X₃).support ≤ Z' := by
  let U : X.Opens := Z.compl
  let W : X.Opens := Z'.compl
  let T := (pushforward U.ι).obj (M.restrict U.ι)
  let a : M ⟶ T := (restrictAdjunction U.ι).unit.app M
  have : T.IsQuasicoherent := QuasicoherentPushforward.quasicoherent_pushforward_of_quasiCompact_separated U.ι _
  let K := kernel a
  let Q := Abelian.coimage a
  have hKq : K.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel a
  have hKt : K.IsFiniteType := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel a
  have hQq : Q.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel (kernel.ι a)
  have hQt : Q.IsFiniteType := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel (kernel.ι a)
  let S := ShortComplex.mk (kernel.ι a) (Abelian.coimage.π a) (by simp)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (kernel.ι a)⟩
  refine ⟨S, hS, rfl, hKq, hKt, hQq, hQt, ?_, ?_⟩
  · exact (coherent_support_le_iff_restrict_compl_isZero K Z).mpr
      (Open.SupportedModules.openRestrictionUnit_kernel_restrict_isZero M U)
  · apply (coherent_support_le_iff_restrict_compl_isZero Q Z').mpr
    apply Open.SupportedModules.module_restrict_isZero_of_mono (Abelian.factorThruCoimage a) W
    apply Open.SupportedModules.openPushforward_restrict_isZero_of_intersection M U W
    apply (ModuleVanishingOpen.module_restrict_isZero_iff_le_vanishingOpen M (U ⊓ W)).mpr
    intro x hx
    by_contra hn
    have hz : x ∈ Z ⊔ Z' := h ((CoherentAnnihilator.coherentAnnihilator_mem_support_iff M x).mpr hn)
    rcases hz with hz | hz
    · exact hx.1 hz
    · exact hx.2 hz

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentSupportSplit
