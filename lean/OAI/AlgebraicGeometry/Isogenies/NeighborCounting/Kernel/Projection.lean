import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

/-! # Projection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Projection

noncomputable section

/-!
Recover a chosen block from the complete kernel by its actual torsion
projector. All opposite and other-place factors disappear by orthogonality.
This connects one-step block kernels to full-kernel quotient definitions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

theorem relativeKernelProduct_comm (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct F G = AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct G F := by
  ext T t a
  constructor <;> rintro ⟨x, hx, y, hy, rfl⟩ <;>
    exact ⟨y, hy, x, hx, mul_comm x y⟩

theorem tupleKernel_contains (s : ℕ) (F : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A)
    (ha : a ∈ (F v).points T t) : a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s F).points T t := by
  induction s with
  | zero => exact Fin.elim0 v
  | succ s ih =>
    refine Fin.cases ?_ (fun v => ?_) v ha
    · intro ha
      exact ⟨a, ha, 1, (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun i => F i.succ)).points T t |>.one_mem,
        (mul_one a).symm⟩
    · intro ha
      exact ⟨1, (F 0).points T t |>.one_mem, a, ih (fun i => F i.succ) v ha,
        (one_mul a).symm⟩

/-- Projection of an iterated product is controlled by projection of its
individual factors, on all test objects. -/
theorem tupleKernel_project_mem (s : ℕ) (F : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (p : A ⟶ A) [IsMonHom p] (K : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (hF : ∀ (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A),
      a ∈ (F v).points T t → a ≫ p ∈ K.points T t)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A)
    (ha : a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s F).points T t) : a ≫ p ∈ K.points T t := by
  induction s generalizing a with
  | zero =>
    change a = 1 at ha
    rw [ha, MonObj.one_comp]
    exact (K.points T t).one_mem
  | succ s ih =>
    obtain ⟨x, hx, y, hy, rfl⟩ := ha
    rw [MonObj.mul_comp]
    exact (K.points T t).mul_mem (hF 0 T t x hx)
      (ih (fun i => F i.succ) (fun i => hF i.succ) y hy)

/-- The paired kernel projects to its chosen factor because the actual
opposite factor is annihilated by the chosen projector. -/
theorem pairedKernel_project_mem (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (p : A ⟶ A) [IsMonHom p] (hF : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F p) (hG : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy G p)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A)
    (ha : a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct F G).points T t) : a ≫ p ∈ F.points T t := by
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  rw [MonObj.mul_comp, hF T t x hx, hG T t y hy, mul_one]
  exact hx

/-- Recover the chosen component of a full tuple without replacing any
opposite subgroup or compact block by its geometric points. -/
theorem chosen_component_of_full_tuple (s : ℕ)
    (F G : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (v : Fin s)
    (p : A ⟶ A) [IsMonHom p]
    (hsupport : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (F v) p) (hopp : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (G v) p)
    (hother : ∀ w, w ≠ v → AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w)) p)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A) (ha : a ≫ p = a) :
    a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun w => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w))).points T t ↔
      a ∈ (F v).points T t := by
  constructor
  · intro h
    have hp := tupleKernel_project_mem s (fun w => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w))
      p (F v) (fun w U u x hx => by
        by_cases hw : w = v
        · subst w
          exact pairedKernel_project_mem (F v) (G v) p hsupport hopp U u x hx
        · rw [hother w hw U u x hx]
          exact (F v).points U u |>.one_mem) T t a h
    rwa [ha] at hp
  · intro h
    apply tupleKernel_contains s (fun w => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w)) v
    exact ⟨a, h, 1, (G v).points T t |>.one_mem, (mul_one a).symm⟩

theorem opposite_component_of_full_tuple (s : ℕ)
    (F G : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (v : Fin s)
    (p : A ⟶ A) [IsMonHom p]
    (hsupport : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn (G v) p) (hchosen : AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (F v) p)
    (hother : ∀ w, w ≠ v → AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.AnnihilatedBy (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w)) p)
    (T : Over S) (t : T ⟶ P) (a : T ⟶ A) (ha : a ≫ p = a) :
    a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun w => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w))).points T t ↔
      a ∈ (G v).points T t := by
  have he : (fun w => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F w) (G w)) =
      (fun w => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (G w) (F w)) :=
    funext (fun w => relativeKernelProduct_comm (F w) (G w))
  rw [he]
  exact chosen_component_of_full_tuple s G F v p hsupport hchosen
    (fun w hw => by rw [relativeKernelProduct_comm]; exact hother w hw) T t a ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Projection
