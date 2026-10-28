import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitGroupScheme
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Split Kernel Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitKernelProjection.CM

noncomputable section

/-! The kernel of a split commutative group map has an actual retraction:
remove the point contributed by the section. This extends its characters
to the full group without losing infinitesimal test points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C] [HasPullbacks C]
  {A B : C} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
  (r : A ⟶ B) [IsMonHom r] (s : B ⟶ A) [IsMonHom s] (hrs : s ≫ r = 𝟙 B)

include hrs in
omit [HasPullbacks C] [IsMonHom s] in
theorem projection_condition : ((𝟙 A) * (r ≫ s)⁻¹) ≫ r = 1 := by
  rw [MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc, hrs,
    Category.comp_id, mul_inv_cancel]

def projection : A ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject r :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv r A).symm ⟨(𝟙 A) * (r ≫ s)⁻¹, projection_condition r s hrs⟩

omit [IsMonHom s] in
theorem projection_inclusion : projection r s hrs ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r = (𝟙 A) * (r ≫ s)⁻¹ :=
  pullback.lift_fst _ _ _

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

instance projection_isMonHom : IsMonHom (projection r s hrs) := by
  have : IsMonHom (projection r s hrs ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r) := by
    rw [projection_inclusion, Hom.mul_def, Hom.inv_def]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r)

theorem inclusion_projection : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ projection r s hrs = 𝟙 (Picard.PoincareBundle.Kernel.Scheme.kernelObject r) := by
  have h : Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ (r ≫ s)⁻¹ = 1 := by
    calc
      _ = (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r ≫ (r ≫ s))⁻¹ := by simp only [Hom.inv_def, Category.assoc]
      _ = 1 := by rw [← Category.assoc, Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.one_comp, inv_one]
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion r)).mp
  rw [Category.assoc, projection_inclusion, MonObj.comp_mul, Category.comp_id, h, mul_one,
    Category.id_comp]

def groupProjection : Grp.mk A ⟶ Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject r) := Grp.ofHom (projection r s hrs)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SplitKernelProjection.CM
