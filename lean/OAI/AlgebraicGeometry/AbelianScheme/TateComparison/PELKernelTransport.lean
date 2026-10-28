import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

/-! # PEL Kernel Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Kernels of transported polarized isogenies, including their chosen
split blocks, as equalities of subgroup functors on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {R : Type u} [CommRing R] {g N : ℕ} {S : Scheme.{u}}
  {A A' B B' : PEL.PELFamilyData R g N S} {n : ℕ}

theorem PELIsogenies.PELIsogeny.kernel_transport (e : PELIsogenies.PELIsogeny A B n)
    (a : PELModuli.PELFamilyIso A' A) (b : PELModuli.PELFamilyIso B B') :
    Subgroups.PointSubgroup.kernel (e.transport a b).isogeny.hom =
      (Subgroups.PointSubgroup.kernel e.isogeny.hom).comapHom a.abelian.hom := by
  apply Subgroups.PointSubgroup.ext
  intro T
  ext x
  change x ≫ (e.transport a b).isogeny.hom = 1 ↔
    (x ≫ a.abelian.hom) ≫ e.isogeny.hom = 1
  rw [PELIsogenies.PELIsogeny.transport_hom, ← Category.assoc, ← Category.assoc]
  exact (Subgroup.groupIsoPoints b.abelian T).map_eq_one_iff

theorem PELIsogenies.PELIsogeny.splitKernel_transport {q : ℕ} [Fact q.Prime]
    (e : PELIsogenies.PELIsogeny A B n) (a : PELModuli.PELFamilyIso A' A) (b : PELModuli.PELFamilyIso B B')
    (χ : R →+* ℤ_[q]) (h : ℕ) :
    (Subgroups.PointSubgroup.kernel (e.transport a b).isogeny.hom).inf (Subgroups.splitBlock A' χ h) =
      ((Subgroups.PointSubgroup.kernel e.isogeny.hom).inf (Subgroups.splitBlock A χ h)).comapHom
        a.abelian.hom := by
  rw [PELIsogenies.PELIsogeny.kernel_transport, Subgroups.PointSubgroup.comap_inf, SplitSubgroups.splitBlock_comapIso]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
