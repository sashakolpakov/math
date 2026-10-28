import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModuleVanishingOpen
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CohomologyExactFiniteness

/-! # Cohomology Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Finiteness transfers through coherent comparison spans once it is
known for coherent sheaves on the closed complement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem CohomologyExactFiniteness.BaseCohomologyFinite.of_iso {X B : Scheme.{u}} (f : X ⟶ B)
    {M N : X.Modules} (e : M ≅ N) (hM : CohomologyExactFiniteness.BaseCohomologyFinite f M) :
    CohomologyExactFiniteness.BaseCohomologyFinite f N := by
  intro n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f N n
  have : Module.Finite Γ(B, ⊤) (SheafCohomology.AffineH.Projective.H M n) := hM n
  apply Module.Finite.of_surjective (CohomologyConnectingScalars.baseCohomologyLinearMap f n e.hom)
  exact (ConcreteCategory.bijective_of_isIso ((SheafCohomology.AffineH.Projective.zariskiFunctor X n).map e.hom)).surjective

theorem CohomologyExactFiniteness.BaseCohomologyFinite.iff_of_kernel_cokernel
    {X B : Scheme.{u}} (f : X ⟶ B) [IsNoetherianRing Γ(B, ⊤)]
    {M N : X.Modules} (a : M ⟶ N)
    (hK : CohomologyExactFiniteness.BaseCohomologyFinite f (kernel a))
    (hC : CohomologyExactFiniteness.BaseCohomologyFinite f (cokernel a)) :
    CohomologyExactFiniteness.BaseCohomologyFinite f M ↔ CohomologyExactFiniteness.BaseCohomologyFinite f N := by
  let S₁ := ShortComplex.mk (kernel.ι a) (Abelian.coimage.π a) (by simp)
  let S₂ := ShortComplex.mk (Abelian.image.ι a) (cokernel.π a) (by simp)
  have hS₁ : S₁.ShortExact := ⟨ShortComplex.cokernelSequence_exact (kernel.ι a)⟩
  have hS₂ : S₂.ShortExact := ⟨ShortComplex.kernelSequence_exact (cokernel.π a)⟩
  constructor
  · intro hM
    have hI := CohomologyExactFiniteness.BaseCohomologyFinite.right f hS₁ hK hM
    exact CohomologyExactFiniteness.BaseCohomologyFinite.middle f hS₂
      (hI.of_iso f (Abelian.coimageIsoImage a)) hC
  · intro hN
    have hI := CohomologyExactFiniteness.BaseCohomologyFinite.left f hS₂ hN hC
    exact CohomologyExactFiniteness.BaseCohomologyFinite.middle f hS₁ hK
      (hI.of_iso f (Abelian.coimageIsoImage a).symm)

theorem CohomologyComparison.module_kernel_restrict_isZero_of_isIso
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor U.ι).map a)] : IsZero ((kernel a).restrict U.ι) := by
  let F := restrictFunctor U.ι
  have : PreservesLimits F := SheafCohomology.Projective.ModuleRestrictLimits.Scheme.Modules.restrictFunctor_preservesLimits U.ι
  exact (PreservesKernel.iso F a).isZero_iff.mpr (isZero_kernel_of_mono (F.map a))

theorem CohomologyComparison.module_cokernel_restrict_isZero_of_isIso
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((restrictFunctor U.ι).map a)] : IsZero ((cokernel a).restrict U.ι) := by
  exact (PreservesCokernel.iso (restrictFunctor U.ι) a).isZero_iff.mpr
    (isZero_cokernel_of_epi ((restrictFunctor U.ι).map a))

/-- This is the comparison step of induction on closed supports. The
induction hypothesis concerns precisely coherent sheaves vanishing on `U`. -/
theorem CohomologyComparison.baseCohomologyFinite_iff_of_open_iso
    {X B : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ B) [IsNoetherianRing Γ(B, ⊤)] (U : X.Opens) [QuasiCompact U.ι]
    (hsmall : ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsFiniteType →
      IsZero (Q.restrict U.ι) → CohomologyExactFiniteness.BaseCohomologyFinite f Q)
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [M.IsFiniteType] [N.IsFiniteType]
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    CohomologyExactFiniteness.BaseCohomologyFinite f M ↔ CohomologyExactFiniteness.BaseCohomologyFinite f N := by
  obtain ⟨K, a, b, hKq, hKt, ha, hb, _⟩ := CoherentComparison.exists_coherent_comparison_span U M N e
  let := hKq
  let := hKt
  let := ha
  let := hb
  have hmap {P Q : X.Modules} [P.IsQuasicoherent] [Q.IsQuasicoherent]
      [P.IsFiniteType] [Q.IsFiniteType] (c : P ⟶ Q)
      [IsIso ((restrictFunctor U.ι).map c)] :
      CohomologyExactFiniteness.BaseCohomologyFinite f P ↔ CohomologyExactFiniteness.BaseCohomologyFinite f Q := by
    exact CohomologyExactFiniteness.BaseCohomologyFinite.iff_of_kernel_cokernel f c
      (hsmall _ (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel c) (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel c)
        (CohomologyComparison.module_kernel_restrict_isZero_of_isIso U c))
      (hsmall _ (SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel c) (SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel c)
        (CohomologyComparison.module_cokernel_restrict_isZero_of_isIso U c))
  exact (hmap a).symm.trans (hmap b)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
