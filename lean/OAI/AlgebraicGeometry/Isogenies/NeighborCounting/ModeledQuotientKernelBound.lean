import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModeledAbelian

/-! # Modeled Quotient Kernel Bound -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The actual complementary morphism bounds the complete scheme kernel
on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {P : Over S}
  {F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P} {R : F.Model} {n : ℕ}

theorem ModeledAbelian.Lifts.ModeledAbelianQuotient.kernel_bound (Q : ModeledAbelian.Lifts.ModeledAbelianQuotient A P F R n)
    (T : Over P.left) (x : T ⟶ (A.pullback P.hom).scheme)
    (hx : x ≫ Q.isogeny.hom = 1) : x ^ n = 1 := by
  have h := congrArg (fun z => x ≫ z) Q.projection_complement
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
