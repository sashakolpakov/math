import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Ab Cochain Classes -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology

noncomputable section

/-! Actual cocycle classes and their naturality for integer complexes of abelian groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

universe u

variable (K : CochainComplex AddCommGrpCat.{u} ℤ) (n : ℤ)

def cycle (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.cycles n :=
  (K.sc n).abCyclesIso.inv ⟨x, by
    change K.d n ((ComplexShape.up ℤ).next n) x = 0
    rw [CochainComplex.next ℤ n]
    exact hx⟩

theorem cycle_i (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    K.iCycles n (cycle K n x hx) = x :=
  (K.sc n).abCyclesIso_inv_apply_iCycles _

def cochainClass (x : K.X n) (hx : K.d n (n + 1) x = 0) : K.homology n :=
  K.homologyπ n (cycle K n x hx)

theorem cochainClass_surjective (a : K.homology n) :
    ∃ (x : K.X n) (hx : K.d n (n + 1) x = 0), cochainClass K n x hx = a := by
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance a
  have hx : K.d n (n + 1) (K.iCycles n z) = 0 :=
    congrArg (fun f : K.cycles n ⟶ K.X (n + 1) => f.hom z) (K.iCycles_d n (n + 1))
  refine ⟨K.iCycles n z, hx, ?_⟩
  have hc : cycle K n (K.iCycles n z) hx = z := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    exact cycle_i K n _ _
  exact (congrArg (K.homologyπ n) hc).trans hz

variable {K} {L : CochainComplex AddCommGrpCat.{u} ℤ} (f : K ⟶ L)

theorem map_closed (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    L.d n (n + 1) (f.f n x) = 0 := by
  have h := congrArg (fun g : K.X n ⟶ L.X (n + 1) => g.hom x) (f.comm n (n + 1))
  simpa only [AddCommGrpCat.comp_apply, hx, map_zero] using h

theorem cycle_naturality (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    cyclesMap f n (cycle K n x hx) = cycle L n (f.f n x) (map_closed n f x hx) := by
  apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  rw [cycle_i]
  have h := congrArg (fun g : K.cycles n ⟶ L.X n => g.hom (cycle K n x hx)) (cyclesMap_i f n)
  simpa only [AddCommGrpCat.comp_apply, cycle_i] using h

theorem cochainClass_naturality (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    homologyMap f n (cochainClass K n x hx) =
      cochainClass L n (f.f n x) (map_closed n f x hx) := by
  have h := congrArg (fun g : K.cycles n ⟶ L.homology n => g.hom (cycle K n x hx))
    (homologyπ_naturality f n)
  simpa only [AddCommGrpCat.comp_apply, cochainClass, cycle_naturality] using h

end

end OAI.AlgebraicGeometry.Comparison.Betti.AbCochainClasses.Homology
