import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.Groups

/-! # Typed Kernel Torsion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TypedKernelTorsion

noncomputable section

/-! The finite module type of an actual etale torsion subgroup forces
its smaller torsion bound on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (R : F.Model) (m n : ℕ)
  (hm : F.KilledBy m) (het : Etale (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A m).hom)

include R hm het in
theorem killedBy_of_geometric
    (hgeo : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (.of K) ⟶ S) (t : Over.mk s ⟶ P) (a : Over.mk s ⟶ A),
        a ∈ F.points (Over.mk s) t → a ^ n = 1) : F.KilledBy n := by
  have : IsMonHom ((𝟙 A) ^ n) := Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 A) n
  have h : R.toGroup ≫ ((𝟙 A) ^ n) = 1 := by
    apply AbelianScheme.IsogenyQuotient.Geometric.Points.Construction.torsion_vanishing_of_geometric_points m R.toGroup (R.toGroup_pow_eq_one hm) _ het
    intro K _ _ s x
    have hx : x ≫ R.toGroup ∈ F.points (Over.mk s) (x ≫ R.toBase) :=
      (R.points_iff _ _ _).mpr ⟨x, rfl, rfl⟩
    have hxpow := hgeo K s (x ≫ R.toBase) (x ≫ R.toGroup) hx
    simpa only [MonObj.comp_pow, Category.comp_id] using hxpow
  have hpow : R.toGroup ^ n = 1 := by
    simpa only [MonObj.comp_pow, Category.comp_id] using h
  intro X t a ha
  obtain ⟨x, _, hx⟩ := (R.points_iff X t a).mp ha
  rw [← hx, ← MonObj.comp_pow, hpow, MonObj.comp_one]

include R hm het in
theorem killedBy_of_moduleType {M : Type u} [AddCommGroup M]
    (hM : ∀ x : M, n • x = 0) (htype : F.HasModuleType M) : F.KilledBy n := by
  apply killedBy_of_geometric F R m n hm het
  intro K _ _ s t a ha
  obtain ⟨e⟩ := htype K s t
  have h : (⟨a, ha⟩ : F.points (Over.mk s) t) ^ n = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact congrArg Multiplicative.ofAdd (hM (e ⟨a, ha⟩).toAdd)
  exact congrArg Subtype.val h

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TypedKernelTorsion
