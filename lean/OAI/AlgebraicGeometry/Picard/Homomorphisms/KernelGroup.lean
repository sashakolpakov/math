import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGeometry
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Kernel Group -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

noncomputable section

/-! The group structure on Homomorphisms's equalizer kernel and its intrinsic Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

attribute [local instance] PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (q : A ⟶ B) [IsMonHom q]

def kernelSchemePullbackIso : Kernel.Construction.kernelScheme q ≅ PoincareBundle.Kernel.Scheme.kernelObject q :=
  (Kernel.Construction.kernelScheme_isPullback q).isoPullback

instance kernelSchemeGroup : GrpObj (Kernel.Construction.kernelScheme q) :=
  GrpObj.ofIso (kernelSchemePullbackIso q).symm

omit [GrpObj A] [IsMonHom q] in
theorem kernelSchemePullbackIso_inclusion :
    (kernelSchemePullbackIso q).hom ≫ PoincareBundle.Kernel.Scheme.kernelInclusion q = Kernel.Construction.kernelInclusion q :=
  (Kernel.Construction.kernelScheme_isPullback q).isoPullback_hom_fst

instance kernelSchemePullbackIso_inv_isMonHom : IsMonHom (kernelSchemePullbackIso q).inv :=
  CategoryTheory.isMonHom_ofIso (kernelSchemePullbackIso q).symm

instance kernelSchemePullbackIso_hom_isMonHom : IsMonHom (kernelSchemePullbackIso q).hom :=
  inferInstanceAs (IsMonHom (kernelSchemePullbackIso q).symm.inv)

instance kernelInclusion_isMonHom : IsMonHom (Kernel.Construction.kernelInclusion q) := by
  rw [← kernelSchemePullbackIso_inclusion q]
  infer_instance

instance kernelInclusion_mono : Mono (Kernel.Construction.kernelInclusion q) :=
  inferInstanceAs (Mono (equalizer.ι q 1))

instance kernelSchemeGroup_commutative [IsCommMonObj A] : IsCommMonObj (Kernel.Construction.kernelScheme q) := by
  apply (isCommMonObj_iff_isMulCommutative _).mpr
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (cancel_mono (Kernel.Construction.kernelInclusion q)).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

omit [GrpObj A] [IsMonHom q] in
theorem kernelInclusion_comp : Kernel.Construction.kernelInclusion q ≫ q = 1 := by
  change equalizer.ι q 1 ≫ q = 1
  rw [equalizer.condition]
  exact MonObj.comp_one _

theorem relativeFrobenius_kernel_frobenius
    (p : ℕ) (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [GrpObj A] :
    Frobenius.Construction.relativeFrobenius p hp hS (Kernel.Construction.kernelScheme (Frobenius.Construction.relativeFrobenius p hp hS A)) = 1 := by
  let F := Frobenius.Construction.relativeFrobenius p hp hS A
  let i := Kernel.Construction.kernelInclusion F
  let P := Over.pullback (Frobenius.Construction.absoluteFrobenius p hp S hS)
  let j : Frobenius.Construction.frobeniusTwist p hp hS (Kernel.Construction.kernelScheme F) ⟶ Frobenius.Construction.frobeniusTwist p hp hS A := P.map i
  have : Mono j := inferInstanceAs (Mono (P.map i))
  have : IsMonHom j := Functor.map.instIsMonHom (F := P) (f := i) (Kernel.Construction.kernelScheme F) A
  apply (cancel_mono j).mp
  have hn := (Group.Construction.relativeFrobeniusNat p hp hS).naturality i
  exact hn.symm.trans ((kernelInclusion_comp F).trans (MonObj.one_comp j).symm)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
