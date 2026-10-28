import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Containment Map -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap

noncomputable section

/-!
# Actual morphisms of represented kernels from scheme-theoretic containment
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {A B D : C} [GrpObj A] [GrpObj B] [GrpObj D]
  (f : A ⟶ B) (g : A ⟶ D) [IsMonHom f] [IsMonHom g]
  (h : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ≫ g = 1)

/-- The kernel universal property constructs the morphism between the actual subgroup objects. -/
def map : Scheme.kernelObject f ⟶ Scheme.kernelObject g :=
  (Scheme.kernelPointsEquiv g (Scheme.kernelObject f)).symm ⟨Scheme.kernelInclusion f, h _ _ (Scheme.kernelInclusion_comp f)⟩

/-- The constructed kernel morphism commutes with the actual inclusions in the ambient group. -/
theorem map_inclusion : map f g h ≫ Scheme.kernelInclusion g = Scheme.kernelInclusion f :=
  pullback.lift_fst _ _ _

attribute [local instance] Scheme.kernelGroup

/-- The morphism constructed from containment is a homomorphism of group objects. -/
instance map_isMonHom : IsMonHom (map f g h) := by
  have : IsMonHom (map f g h ≫ Scheme.kernelInclusion g) := by rw [map_inclusion]; infer_instance
  exact Splitting.isMonHom_of_mono_postcomp _ (Scheme.kernelInclusion g)

/-- Scheme-theoretic containment gives an actual monomorphism of the represented kernels. -/
instance map_mono : Mono (map f g h) := by
  constructor
  intro T a b hab
  apply (cancel_mono (Scheme.kernelInclusion f)).mp
  rw [← map_inclusion f g h, ← Category.assoc, ← Category.assoc, hab]

/-- Every test point of the smaller kernel has the same ambient point after the constructed inclusion. -/
theorem point_inclusion {T : C} (k : T ⟶ Scheme.kernelObject f) :
    (k ≫ map f g h) ≫ Scheme.kernelInclusion g = k ≫ Scheme.kernelInclusion f := by
  rw [Category.assoc, map_inclusion]

variable [BraidedCategory C] [IsCommMonObj A]

/-- Torsion containment constructs a morphism into the actual n-torsion subgroup scheme. -/
def torsionMap (n : ℕ) (hn : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    Scheme.kernelObject f ⟶ Scheme.kernelObject ((𝟙 A) ^ n) :=
  map f ((𝟙 A) ^ n) (fun T x hx => by rw [MonObj.comp_pow, Category.comp_id]; exact hn T x hx)

/-- The torsion inclusion retains the actual included scheme point on every test scheme. -/
theorem torsionMap_inclusion (n : ℕ) (hn : ∀ (T : C) (x : T ⟶ A), x ≫ f = 1 → x ^ n = 1) :
    torsionMap f n hn ≫ Scheme.kernelInclusion ((𝟙 A) ^ n) = Scheme.kernelInclusion f :=
  map_inclusion f ((𝟙 A) ^ n) _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentMap
