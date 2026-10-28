import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.TorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafComparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

/-! # Character Torsion Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterTorsionComparison

noncomputable section

/-!
The original multiplication kernel used for character-line descent and
TorsionQuotient's torsion equalizer both identify with IsogenyQuotient's native torsion group.
The comparisons preserve the actual inclusion into the source scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

namespace Construction

universe u

theorem torsionGroup_eq_of_group_eq {S : Scheme.{u}} (X : Over S)
    (g₁ g₂ : GrpObj X) (c₁ : letI := g₁; IsCommMonObj X)
    (c₂ : letI := g₂; IsCommMonObj X) (hg : g₁ = g₂) (n : ℕ) :
    (letI := g₁; letI : IsCommMonObj X := c₁;
      CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk X) n) =
    (letI := g₂; letI : IsCommMonObj X := c₂;
      CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk X) n) := by
  subst g₂
  rfl

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

instance torsionEqualizerKernelIso_hom_isMonHom : IsMonHom (Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n).hom := by
  have : IsMonHom ((Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n).hom ≫ Torsion.Groups.Construction.nativeTorsionInclusion G.X n) := by
    rw [Intrinsic.TorsionComparison.Construction.torsionEqualizerKernelIso_hom_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (Torsion.Groups.Construction.nativeTorsionInclusion G.X n)

def equalizerTorsionKernelGroupIso :
    CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n ≅ Torsion.SheafComparison.Construction.kernelTorsionGroup G n :=
  Grp.mkIso' (Torsion.Groups.Construction.torsionEqualizerKernelIso G.X n)

def multiplicationKernelNativeGroupIso :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 G.X) ^ n)) ≅ Torsion.SheafComparison.Construction.kernelTorsionGroup G n :=
  Grp.mkIso' (Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 G.X) ^ n))

theorem multiplicationKernelNativeGroupIso_inclusion :
    (multiplicationKernelNativeGroupIso G n).hom.hom.hom ≫ Torsion.Groups.Construction.nativeTorsionInclusion G.X n =
      Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n) :=
  Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso_inclusion ((𝟙 G.X) ^ n)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterTorsionComparison
