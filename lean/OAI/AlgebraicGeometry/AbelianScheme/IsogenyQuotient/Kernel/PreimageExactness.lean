import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.PreimageQuotient
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Preimage Exactness -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageExactness.Construction

noncomputable section

/-! The original quotient kernel is exactly the kernel of its
restriction to an inverse-image kernel, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

universe u
variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
  (f : A ⟶ B) [IsMonHom f] (r : B ⟶ C) [IsMonHom r]

def kernelPreimageInclusion : Picard.PoincareBundle.Kernel.Scheme.kernelObject f ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r) :=
  Picard.PoincareBundle.Kernel.ContainmentMap.map f (f ≫ r) (fun _T x hx => by rw [← Category.assoc, hx, MonObj.one_comp])

theorem kernelPreimageInclusion_inclusion :
    kernelPreimageInclusion f r ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (f ≫ r) = Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f :=
  Picard.PoincareBundle.Kernel.ContainmentMap.map_inclusion f (f ≫ r) _

instance kernelPreimageInclusion_isMonHom : IsMonHom (kernelPreimageInclusion f r) :=
  inferInstanceAs (IsMonHom (Picard.PoincareBundle.Kernel.ContainmentMap.map f (f ≫ r) _))

instance kernelPreimageInclusion_mono : Mono (kernelPreimageInclusion f r) :=
  inferInstanceAs (Mono (Picard.PoincareBundle.Kernel.ContainmentMap.map f (f ≫ r) _))

theorem kernelPreimageInclusion_comp : kernelPreimageInclusion f r ≫ Picard.PoincareBundle.Kernel.PreimageQuotient.map f r = 1 := by
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r)).mp
  rw [Category.assoc, Picard.PoincareBundle.Kernel.PreimageQuotient.map_inclusion, ← Category.assoc,
    kernelPreimageInclusion_inclusion, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.one_comp]

theorem kernelPreimage_kernel_iff (T : Over S) (x : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (f ≫ r)) :
    x ≫ Picard.PoincareBundle.Kernel.PreimageQuotient.map f r = 1 ↔
      ∃! a : T ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject f, a ≫ kernelPreimageInclusion f r = x := by
  constructor
  · intro hx
    have hxF : (x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (f ≫ r)) ≫ f = 1 := by
      have hp := congrArg (fun a => a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) hx
      rw [Category.assoc, Picard.PoincareBundle.Kernel.PreimageQuotient.map_inclusion, MonObj.one_comp] at hp
      exact (Category.assoc _ _ _).trans hp
    let a := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f T).symm ⟨x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (f ≫ r), hxF⟩
    have ha : a ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f = x ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (f ≫ r) :=
      congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f T).apply_symm_apply ⟨_, hxF⟩)
    have hai : a ≫ kernelPreimageInclusion f r = x := by
      apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (f ≫ r))).mp
      rw [Category.assoc, kernelPreimageInclusion_inclusion]
      exact ha
    exact ⟨a, hai, fun b hb => (cancel_mono (kernelPreimageInclusion f r)).mp (hb.trans hai.symm)⟩
  · rintro ⟨a, ha, _⟩
    rw [← ha, Category.assoc, kernelPreimageInclusion_comp, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.PreimageExactness.Construction
