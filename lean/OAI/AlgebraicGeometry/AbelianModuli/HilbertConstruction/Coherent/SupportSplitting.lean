import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SupportedModules
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.Annihilator
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.QuasicoherentKernels

/-! # Support Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportSplitting

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

open _root_.TopologicalSpace

theorem coherent_support_le_iff_restrict_compl_isZero
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (Z : Closeds X) :
    (Annihilator.coherentAnnihilator M).support ≤ Z ↔
      IsZero (M.restrict (Scheme.Opens.ι (X := X) Z.compl)) := by
  rw [Module.VanishingOpen.module_restrict_isZero_iff_le_vanishingOpen]
  constructor
  · intro h x hx
    by_contra hn
    exact hx (h ((Annihilator.coherentAnnihilator_mem_support_iff M x).mpr hn))
  · intro h x hx
    by_contra hn
    exact (Annihilator.coherentAnnihilator_mem_support_iff M x).mp hx (h hn)

theorem exists_coherent_support_split
    {X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (Z Z' : Closeds X) (h : (Annihilator.coherentAnnihilator M).support ≤ Z ⊔ Z') :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧ S.X₂ = M ∧
      ∃ (_h₁ : S.X₁.IsQuasicoherent) (_h₂ : S.X₁.IsFiniteType)
        (_h₃ : S.X₃.IsQuasicoherent) (_h₄ : S.X₃.IsFiniteType),
        (Annihilator.coherentAnnihilator S.X₁).support ≤ Z ∧
        (Annihilator.coherentAnnihilator S.X₃).support ≤ Z' := by
  let U : X.Opens := Z.compl
  let W : X.Opens := Z'.compl
  let T := (pushforward U.ι).obj (M.restrict U.ι)
  let a : M ⟶ T := (restrictAdjunction U.ι).unit.app M
  have : T.IsQuasicoherent := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent U.ι _
  let K := kernel a
  let Q := Abelian.coimage a
  have hKq : K.IsQuasicoherent := Quasicoherent.Kernels.module_quasicoherent_kernel a
  have hKt : K.IsFiniteType := Noetherian.QuasicoherentKernels.noetherian_quasicoherent_kernel_finiteType a
  have hQq : Q.IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel (kernel.ι a)
  have hQt : Q.IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType (kernel.ι a)
  let S := ShortComplex.mk (kernel.ι a) (Abelian.coimage.π a) (by simp)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact (kernel.ι a)⟩
  refine ⟨S, hS, rfl, hKq, hKt, hQq, hQt, ?_, ?_⟩
  · exact (coherent_support_le_iff_restrict_compl_isZero K Z).mpr
      (Open.SupportedModules.openRestrictionUnit_kernel_restrict_isZero M U)
  · apply (coherent_support_le_iff_restrict_compl_isZero Q Z').mpr
    apply Open.SupportedModules.module_restrict_isZero_of_mono (Abelian.factorThruCoimage a) W
    apply Open.SupportedModules.openPushforward_restrict_isZero_of_intersection M U W
    apply (Module.VanishingOpen.module_restrict_isZero_iff_le_vanishingOpen M (U ⊓ W)).mpr
    intro x hx
    by_contra hn
    have hz : x ∈ Z ⊔ Z' := h ((Annihilator.coherentAnnihilator_mem_support_iff M x).mpr hn)
    rcases hz with hz | hz
    · exact hx.1 hz
    · exact hx.2 hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coherent.SupportSplitting
