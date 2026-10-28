import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.KernelNilpotence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReductionKernelRestriction

/-! # Global Kernel Nilpotence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalKernelNilpotence

noncomputable section

/-! The actual coherent kernel lowers the global annihilating ideal
exponent. The local-to-global argument uses the canonical unit comparison. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

theorem closedReductionKernel_power_annihilates
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ)
    (h : f.ker ^ (n + 1) ≤ CoherentAnnihilator.coherentAnnihilator M) :
    letI := ClosedReductionLayer.closedReductionKernel_quasicoherent f M
    letI := ClosedReductionLayer.closedReductionKernel_finiteType f M
    f.ker ^ n ≤ CoherentAnnihilator.coherentAnnihilator (ClosedReductionLayer.closedReductionKernel f M) := by
  have := ClosedReductionLayer.closedReductionKernel_quasicoherent f M
  have := ClosedReductionLayer.closedReductionKernel_finiteType f M
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let V : Y.affineOpens := ⟨U.1.ι ''ᵁ ⊤, by rw [U.1.ι_image_top]; exact U.2⟩
  have hlocal : (RingHom.ker (f ∣_ U.1).appTop.hom) ^ (n + 1) ≤
      Module.annihilator Γ(U.1.toScheme, ⊤) Γ(M.restrict U.1.ι, ⊤) := by
    rw [Affine.KernelNilpotence.morphismRestrict_appTop_ker, Affine.KernelNilpotence.module_restrict_top_annihilator]
    have hV := h V
    change (f.ker.ideal V) ^ (n + 1) ≤ Module.annihilator Γ(Y, V.1) Γ(M, V.1) at hV
    rw [Scheme.Hom.ker_apply] at hV
    exact hV
  have hk := Affine.KernelNilpotence.affineReductionKernel_power_annihilates (f ∣_ U.1)
    ((f ∣_ U.1).app_surjective ⊤ (isAffineOpen_top _)) (M.restrict U.1.ι) n hlocal
  let e := (SheafOfModules.evaluation U.1.toScheme.ringCatSheaf (op ⊤)).mapIso
    (ReductionKernelRestriction.closedReductionKernelRestrictIso f U.1 M)
  have hk' : (RingHom.ker (f ∣_ U.1).appTop.hom) ^ n ≤
      Module.annihilator Γ(U.1.toScheme, ⊤)
        Γ((ClosedReductionLayer.closedReductionKernel f M).restrict U.1.ι, ⊤) :=
    hk.trans (e.toLinearEquiv.toLinearMap.annihilator_le_of_injective e.toLinearEquiv.injective)
  rw [Affine.KernelNilpotence.morphismRestrict_appTop_ker, Affine.KernelNilpotence.module_restrict_top_annihilator] at hk'
  have hV : (f.ker.ideal V) ^ n ≤ (CoherentAnnihilator.coherentAnnihilator (ClosedReductionLayer.closedReductionKernel f M)).ideal V := by
    change (f.ker.ideal V) ^ n ≤ Module.annihilator Γ(Y, V.1) Γ(ClosedReductionLayer.closedReductionKernel f M, V.1)
    rw [Scheme.Hom.ker_apply]
    exact hk'
  have hVU : V = U := Subtype.ext U.1.ι_image_top
  exact (congrArg (fun W : Y.affineOpens =>
    (f.ker ^ n).ideal W ≤ (CoherentAnnihilator.coherentAnnihilator (ClosedReductionLayer.closedReductionKernel f M)).ideal W) hVU).mp hV

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalKernelNilpotence
