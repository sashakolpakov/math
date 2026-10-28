import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClasses

/-! # Total Filtration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration

noncomputable section

/-! The row filtration on the original total cohomology and its row-class maps. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates

universe u v

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  [K.HasTotal (.up ℕ)]

def cycles (n q : ℕ) : Submodule R (CochainClasses.cycles (K.total (.up ℕ)) n) where
  carrier := {x | TotalCoordinates.ZeroRowsBefore K n x.val q}
  zero_mem' := by intro a b _ _; exact map_zero _
  add_mem' := by
    intro x y hx hy a b hab ha
    change (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b n (x.val + y.val) = 0
    rw [map_add, hx a b hab ha, hy a b hab ha, add_zero]
  smul_mem' := by
    intro r x hx a b hab ha
    change ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b n).hom (r • x.val) = 0
    rw [map_smul, hx a b hab ha, smul_zero]

def classMap (n q : ℕ) : cycles K n q →ₗ[R] (K.total (.up ℕ)).homology n :=
  (CochainClasses.classMap (K.total (.up ℕ)) n).comp (cycles K n q).subtype

abbrev image (n q : ℕ) : Submodule R ((K.total (.up ℕ)).homology n) := (classMap K n q).range

def rowCycleMap (n q p : ℕ) (hdeg : q + p = n) :
    cycles K n q →ₗ[R] CochainClasses.cycles (K.X q) p :=
  ((((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q p n).hom.comp
    (CochainClasses.cycles (K.total (.up ℕ)) n).subtype).comp
      (cycles K n q).subtype).codRestrict _
        (fun x => TotalCoordinates.cycle_row K n q p hdeg x.val.val x.val.property x.property)

def rowClassMap (n q p : ℕ) (hdeg : q + p = n) :
    cycles K n q →ₗ[R] (K.X q).homology p :=
  (CochainClasses.classMap (K.X q) p).comp (rowCycleMap K n q p hdeg)

theorem image_zero (n : ℕ) : image K n 0 = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro ξ
  obtain ⟨x, hx⟩ := CochainClasses.classMap_surjective (K.total (.up ℕ)) n ξ
  exact ⟨⟨x, by intro a b _ ha; omega⟩, hx⟩

theorem cycles_last_eq_zero (n : ℕ) (x : cycles K n (n + 1)) : x = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  apply TotalCoordinates.eq_zero_of_coordinates K n x.val.val
  intro i
  exact x.property i (n - i) (by omega) i.isLt

theorem image_last (n : ℕ) : image K n (n + 1) = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  ext x
  rw [cycles_last_eq_zero K n x, map_zero]
  rfl

theorem zero_row_class_lifts (n q p : ℕ) (hdeg : q + p = n)
    (x : cycles K n q) (hx : rowClassMap K n q p hdeg x = 0) :
    ∃ y : cycles K n (q + 1), classMap K n (q + 1) y = classMap K n q x := by
  cases p with
  | zero =>
      have hrow : (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q 0 n x.val.val = 0 := by
        have h := (CochainClasses.classMap_zero_eq_zero_iff (K.X q)
          (rowCycleMap K n q 0 hdeg x)).mp hx
        exact congrArg Subtype.val h
      have hy : TotalCoordinates.ZeroRowsBefore K n x.val.val (q + 1) := by
        intro a b hab ha
        by_cases haq : a < q
        · exact x.property a b hab haq
        · have heqa : a = q := by omega
          have heqb : b = 0 := by omega
          subst a b
          exact hrow
      exact ⟨⟨x.val, hy⟩, rfl⟩
  | succ p =>
      have hn : n = q + p + 1 := by omega
      cases hn
      obtain ⟨y, hy⟩ := (CochainClasses.classMap_succ_eq_zero_iff (K.X q) p
        (rowCycleMap K (q + p + 1) q (p + 1) hdeg x)).mp hx
      obtain ⟨z, hz⟩ := TotalCoordinates.remove_boundary_coordinate K q p x.val.val y hy x.property
      have hc : (K.total (.up ℕ)).d (q + p + 1) (q + p + 1 + 1)
          (x.val.val - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) = 0 := by
        rw [map_sub, x.val.property]
        have hd := congrArg (fun f => f z)
          ((K.total (.up ℕ)).d_comp_d (q + p) (q + p + 1) (q + p + 1 + 1))
        change (K.total (.up ℕ)).d (q + p + 1) (q + p + 1 + 1)
          ((K.total (.up ℕ)).d (q + p) (q + p + 1) z) = 0 at hd
        rw [hd, sub_self]
      let x' : cycles K (q + p + 1) (q + 1) := ⟨⟨_, hc⟩, hz⟩
      refine ⟨x', Eq.symm ?_⟩
      change CochainClasses.classMap (K.total (.up ℕ)) (q + p + 1) x.val =
        CochainClasses.classMap (K.total (.up ℕ)) (q + p + 1) x'.val
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply (CochainClasses.classMap_succ_eq_zero_iff (K.total (.up ℕ))
        (q + p) (x.val - x'.val)).mpr
      exact ⟨z, by change _ = x.val.val - (x.val.val - _); abel⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration
