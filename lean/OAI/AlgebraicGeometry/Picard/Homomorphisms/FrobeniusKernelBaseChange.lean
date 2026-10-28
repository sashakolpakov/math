import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelBaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusBaseChange

/-! # Frobenius Kernel Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange

noncomputable section

/-! The geometric fibers of the original Frobenius kernel are the native
Frobenius kernels of the corresponding geometric fibers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B C T : Over S} [GrpObj B] [GrpObj C]

def kernelLift (q : A ⟶ B) (a : T ⟶ A) (ha : a ≫ q = 1) : T ⟶ Kernel.Construction.kernelScheme q :=
  equalizer.lift a (ha.trans (MonObj.comp_one a).symm)

@[reassoc (attr := simp)]
theorem kernelLift_inclusion (q : A ⟶ B) (a : T ⟶ A) (ha : a ≫ q = 1) :
    kernelLift q a ha ≫ Kernel.Construction.kernelInclusion q = a := equalizer.lift_ι _ _

def kernelTargetIso (q : A ⟶ B) (r : A ⟶ C) (e : B ≅ C) [IsMonHom e.hom]
    (he : q ≫ e.hom = r) : Kernel.Construction.kernelScheme q ≅ Kernel.Construction.kernelScheme r where
  hom := kernelLift r (Kernel.Construction.kernelInclusion q) (by
    rw [← he, ← Category.assoc, KernelGroup.Construction.kernelInclusion_comp, MonObj.one_comp])
  inv := kernelLift q (Kernel.Construction.kernelInclusion r) (by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, he, KernelGroup.Construction.kernelInclusion_comp, MonObj.one_comp])
  hom_inv_id := by
    apply (cancel_mono (Kernel.Construction.kernelInclusion q)).mp
    simp only [Category.assoc, kernelLift_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (Kernel.Construction.kernelInclusion r)).mp
    simp only [Category.assoc, kernelLift_inclusion, Category.id_comp]

@[reassoc (attr := simp)]
theorem kernelTargetIso_hom_inclusion
    (q : A ⟶ B) (r : A ⟶ C) (e : B ≅ C) [IsMonHom e.hom] (he : q ≫ e.hom = r) :
    (kernelTargetIso q r e he).hom ≫ Kernel.Construction.kernelInclusion r = Kernel.Construction.kernelInclusion q := by
  dsimp only [kernelTargetIso]
  exact kernelLift_inclusion _ _ _

@[reassoc (attr := simp)]
theorem kernelTargetIso_inv_inclusion
    (q : A ⟶ B) (r : A ⟶ C) (e : B ≅ C) [IsMonHom e.hom] (he : q ≫ e.hom = r) :
    (kernelTargetIso q r e he).inv ≫ Kernel.Construction.kernelInclusion q = Kernel.Construction.kernelInclusion r := by
  dsimp only [kernelTargetIso]
  exact kernelLift_inclusion _ _ _

variable (p : ℕ) (hp : p.Prime) {U : Scheme.{u}}
variable (hS : (p : Γ(S, ⊤)) = 0) (s : U ⟶ S) (A : Over S) [GrpObj A] [Smooth A.hom]

/-- The comparison retains the entire scheme structure, for any base change. -/
def relativeFrobeniusKernelBaseChangeIso :
    (Over.pullback s).obj (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp hS A)) ≅
      Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s)
        ((Over.pullback s).obj A)) :=
  KernelBaseChange.Construction.kernelBaseChangeIso s (Frobenius.Construction.relativeFrobenius p hp hS A) ≪≫
    (kernelTargetIso
      (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s) ((Over.pullback s).obj A))
      ((Over.pullback s).map (Frobenius.Construction.relativeFrobenius p hp hS A))
      (FrobeniusBaseChange.Construction.frobeniusTwistBaseChangeIso p hp hS s A)
      (FrobeniusBaseChange.Construction.relativeFrobenius_baseChange p hp hS s A)).symm

theorem relativeFrobeniusKernelBaseChangeIso_inclusion :
    (relativeFrobeniusKernelBaseChangeIso p hp hS s A).hom ≫
      Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p hp (Frobenius.Construction.prime_eq_zero_of_map p hS s)
        ((Over.pullback s).obj A)) =
      (Over.pullback s).map (Kernel.Construction.kernelInclusion (Frobenius.Construction.relativeFrobenius p hp hS A)) := by
  dsimp only [relativeFrobeniusKernelBaseChangeIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, kernelTargetIso_inv_inclusion, KernelBaseChange.Construction.kernelBaseChangeIso_inclusion]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FrobeniusKernelBaseChange
