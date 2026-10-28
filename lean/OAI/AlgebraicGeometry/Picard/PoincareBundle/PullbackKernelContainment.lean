import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

/-! # Pullback Kernel Containment -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackKernelContainment

noncomputable section

/-! The actual polarization pullback identity constructs both kernel inclusions into its full kernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B D Z : C} [GrpObj A] [GrpObj B] [GrpObj D] [GrpObj Z]
  (f : A ⟶ B) [IsMonHom f] (m : B ⟶ D) [IsMonHom m] (g : D ⟶ Z) [IsMonHom g]
  (φ : A ⟶ Z) [IsMonHom φ] (h : f ≫ m ≫ g = φ)

include h

omit [HasPullbacks C] [GrpObj A] [GrpObj B] [IsMonHom f] [IsMonHom m] [IsMonHom φ] in
/-- Every point in the full inverse-image kernel is killed by the original composite polarization. -/
theorem inverseImage_killed (T : C) (x : T ⟶ A) (hx : x ≫ (f ≫ m) = 1) : x ≫ φ = 1 := by
  rw [← h, ← Category.assoc f m g, ← Category.assoc x (f ≫ m) g, hx, MonObj.one_comp]

omit [HasPullbacks C] [GrpObj A] [IsMonHom f] [IsMonHom φ] in
/-- The identity-composed quotient kernel is killed by the original polarization on every test object. -/
theorem quotientKernel_killed (T : C) (x : T ⟶ A) (hx : x ≫ (f ≫ 𝟙 B) = 1) : x ≫ φ = 1 := by
  have hx' : x ≫ f = 1 := by simpa only [Category.comp_id] using hx
  rw [← h, ← Category.assoc x f (m ≫ g), hx', MonObj.one_comp]

omit [IsMonHom φ] in
/-- The first full kernel annihilation follows directly from the pullback identity. -/
theorem inverseImage_annihilation : Kernel.Scheme.kernelInclusion (f ≫ m) ≫ φ = 1 :=
  inverseImage_killed f m g φ h _ _ (Kernel.Scheme.kernelInclusion_comp (f ≫ m))

omit [IsMonHom φ] in
/-- The quotient kernel annihilation follows directly from the same identity. -/
theorem quotientKernel_annihilation : Kernel.Scheme.kernelInclusion (f ≫ 𝟙 B) ≫ φ = 1 :=
  quotientKernel_killed f m g φ h _ _ (Kernel.Scheme.kernelInclusion_comp (f ≫ 𝟙 B))

/-- The universal property constructs the actual inverse-image kernel inclusion into the polarization kernel. -/
def inverseImageMap : Kernel.Scheme.kernelObject (f ≫ m) ⟶ Kernel.Scheme.kernelObject φ :=
  Kernel.ContainmentMap.map (f ≫ m) φ (inverseImage_killed f m g φ h)

/-- Its actual ambient scheme coordinate is unchanged. -/
theorem inverseImageMap_inclusion : inverseImageMap f m g φ h ≫ Kernel.Scheme.kernelInclusion φ = Kernel.Scheme.kernelInclusion (f ≫ m) :=
  Kernel.ContainmentMap.map_inclusion (f ≫ m) φ (inverseImage_killed f m g φ h)

/-- The quotient kernel likewise maps into the actual full polarization kernel. -/
def quotientKernelMap : Kernel.Scheme.kernelObject (f ≫ 𝟙 B) ⟶ Kernel.Scheme.kernelObject φ :=
  Kernel.ContainmentMap.map (f ≫ 𝟙 B) φ (quotientKernel_killed f m g φ h)

/-- The quotient-kernel inclusion retains its actual ambient coordinate. -/
theorem quotientKernelMap_inclusion : quotientKernelMap f m g φ h ≫ Kernel.Scheme.kernelInclusion φ = Kernel.Scheme.kernelInclusion (f ≫ 𝟙 B) :=
  Kernel.ContainmentMap.map_inclusion (f ≫ 𝟙 B) φ (quotientKernel_killed f m g φ h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackKernelContainment
