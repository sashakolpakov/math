import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescribed
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Kernel Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.KernelBaseChange.Construction

noncomputable section

/-! Base change of the actual native scheme kernel, with its original
inclusion. Equalizer preservation keeps the full nonreduced structure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S T : Scheme.{u}} {A B H : Over S} [GrpObj A] [GrpObj B]
variable (f : T ⟶ S) (p : A ⟶ B) (i : H ⟶ A) [Mono i]

omit [GrpObj A] in
/-- The original universal kernel condition survives arbitrary base
change, for group schemes without a smoothness or reducedness premise. -/
theorem prescribedKernel_pullback (hp : Prescribed.Construction.PrescribedKernel p i) :
    Prescribed.Construction.PrescribedKernel ((Over.pullback f).map p) ((Over.pullback f).map i) := by
  let F := Over.pullback f
  let hlim := isLimitForkMapOfIsLimit F _ (Prescribed.Construction.prescribedKernelForkIsLimit p i hp)
  intro U a
  constructor
  · intro ha
    have hc : a ≫ F.map p = a ≫ F.map (1 : A ⟶ B) := by
      rw [F.map_one, MonObj.comp_one]
      exact ha
    obtain ⟨z, hz⟩ := Fork.IsLimit.lift' hlim a hc
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact (cancel_mono (F.map i)).mp (hw.trans hz.symm)
  · rintro ⟨z, hz, _⟩
    rw [← hz, Category.assoc, ← F.map_comp, Prescribed.Construction.prescribedKernel_kills p i hp,
      F.map_one, MonObj.comp_one]

variable [IsMonHom p]

omit f in
theorem nativeKernel_prescribed : Prescribed.Construction.PrescribedKernel p (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p) := by
  intro U a
  constructor
  · intro ha
    let z := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv p U).symm ⟨a, ha⟩
    have hz : z ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p = a :=
      congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv p U).apply_symm_apply ⟨a, ha⟩)
    refine ⟨z, hz, ?_⟩
    intro w hw
    exact (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p)).mp (hw.trans hz.symm)
  · rintro ⟨z, hz, _⟩
    rw [← hz, Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]

/-- Comparison with the pullback-over-the-identity definition of the
native kernel. The isomorphism is constructed from the two universal properties. -/
def nativePrescribedKernelIso (hp : Prescribed.Construction.PrescribedKernel p i) : H ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject p :=
  Prescribed.Construction.prescribedKernelIso p i hp ≪≫
    (Prescribed.Construction.prescribedKernelIso p (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p) (nativeKernel_prescribed p)).symm

theorem nativePrescribedKernelIso_inclusion (hp : Prescribed.Construction.PrescribedKernel p i) :
    (nativePrescribedKernelIso p i hp).hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p = i := by
  change ((Prescribed.Construction.prescribedKernelIso p i hp).hom ≫
    (Prescribed.Construction.prescribedKernelIso p (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p) (nativeKernel_prescribed p)).inv) ≫ _ = _
  have hi : (Prescribed.Construction.prescribedKernelIso p (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p)
      (nativeKernel_prescribed p)).inv ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p =
        Picard.Homomorphisms.Kernel.Construction.kernelInclusion p := by
    apply (Iso.inv_comp_eq _).mpr
    exact (Prescribed.Construction.prescribedKernelIso_inclusion p (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p)
      (nativeKernel_prescribed p)).symm
  rw [Category.assoc, hi]
  exact Prescribed.Construction.prescribedKernelIso_inclusion p i hp

/-- The actual kernel scheme commutes with every base change. -/
def nativeKernelBaseChangeIso :
    (Over.pullback f).obj (Picard.PoincareBundle.Kernel.Scheme.kernelObject p) ≅
      Picard.PoincareBundle.Kernel.Scheme.kernelObject ((Over.pullback f).map p) :=
  nativePrescribedKernelIso ((Over.pullback f).map p)
    ((Over.pullback f).map (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p))
    (prescribedKernel_pullback f p (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p) (nativeKernel_prescribed p))

theorem nativeKernelBaseChangeIso_inclusion :
    (nativeKernelBaseChangeIso f p).hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback f).map p) =
      (Over.pullback f).map (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p) :=
  nativePrescribedKernelIso_inclusion _ _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.KernelBaseChange.Construction
