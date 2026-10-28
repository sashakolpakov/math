import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.CochainClassNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration
import Mathlib.Algebra.Homology.Additive

/-! # Total Second Classes -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondClasses

noncomputable section

/-! A filtered total cycle gives an actual horizontal cohomology class of the row homology complex. -/

open _root_.CategoryTheory Limits

open OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiltration

universe u v

variable {R : Type u} [CommRing R]
  (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)]

def horizontal (p : ℕ) : CochainComplex (ModuleCat.{v} R) ℕ :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℕ) p).mapHomologicalComplex (.up ℕ)).obj K

theorem horizontal_cycle (n q p : ℕ) (hdeg : q + p = n) (x : TotalFiltration.cycles K n q) :
    (horizontal K p).d q (q + 1) (TotalFiltration.rowClassMap K n q p hdeg x) = 0 := by
  change HomologicalComplex.homologyMap (K.d q (q + 1)) p
    (CochainClasses.classMap (K.X q) p (TotalFiltration.rowCycleMap K n q p hdeg x)) = 0
  rw [← CochainClassNaturality.naturality_apply]
  cases p with
  | zero =>
      have hn : n = q := by omega
      subst n
      apply (CochainClasses.classMap_zero_eq_zero_iff (K.X (q + 1)) _).mpr
      apply Subtype.ext
      change (K.d q (q + 1)).f 0 ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q 0 q x.val.val) = 0
      have h := congrArg (fun f => f x.val.val) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_zero_right K q)
      have hc := x.val.property
      change (K.total (.up ℕ)).d q (q + 1) x.val.val = 0 at hc
      simpa only [ConcreteCategory.comp_apply, hc, map_zero] using h.symm
  | succ p =>
      have hn : n = q + p + 1 := by omega
      cases hn
      let y := (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) (q + 1) p (q + p + 1) x.val.val
      let r : ℤˣ := (-1) ^ (q + 1)
      have he : (K.d q (q + 1)).f (p + 1)
          ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1) x.val.val) +
        r • (K.X (q + 1)).d p (p + 1) y = 0 := by
        have h := congrArg (fun f => f x.val.val) (AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatBoundary.Projective.total_d_π_interior K q p)
        have hc := x.val.property
        change (K.total (.up ℕ)).d (q + p + 1) (q + p + 1 + 1) x.val.val = 0 at hc
        simpa [ConcreteCategory.comp_apply, hc, r, y, Units.smul_def] using h.symm
      apply (CochainClasses.classMap_succ_eq_zero_iff (K.X (q + 1)) p _).mpr
      refine ⟨-(r.val • y), ?_⟩
      change (K.X (q + 1)).d p (p + 1) (-(r.val • y)) =
        (K.d q (q + 1)).f (p + 1) ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q (p + 1) (q + p + 1) x.val.val)
      rw [map_neg]
      have hs := ((K.X (q + 1)).d p (p + 1)).hom.toAddMonoidHom.map_zsmul r.val y
      exact (congrArg (fun z => -z) hs).trans (eq_neg_of_add_eq_zero_left he).symm

def secondCycleMap (n q p : ℕ) (hdeg : q + p = n) :
    TotalFiltration.cycles K n q →ₗ[R] CochainClasses.cycles (horizontal K p) q :=
  (TotalFiltration.rowClassMap K n q p hdeg).codRestrict _ (horizontal_cycle K n q p hdeg)

def secondClassMap (n q p : ℕ) (hdeg : q + p = n) :
    TotalFiltration.cycles K n q →ₗ[R] (horizontal K p).homology q :=
  (CochainClasses.classMap (horizontal K p) q).comp (secondCycleMap K n q p hdeg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalSecondClasses
