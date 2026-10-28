import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomAcyclicProducts
import OAI.NumberTheory.PadicHodge.IntegralComparison.TotalComponentLift
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Total Kernel Hom Rows -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TotalKernelHomRows

noncomputable section

/-! The kernel of the zeroth Čech-column projection has exact Hom rows
whenever every positive-column coefficient has exact Hom rows. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) [K.HasTotal (.up ℕ)] (n : ℕ)

abbrev projection := (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) n 0 n

theorem factor {A B : C} (d : A ⟶ B) (f : A ⟶ kernel (projection K n))
    (hf : ∀ p q (_h : p + q = n), q ≠ 0 →
      ∃ g : B ⟶ (K.X p).X q, d ≫ g = f ≫ kernel.ι (projection K n) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) p q n) :
    ∃ g : B ⟶ kernel (projection K n), d ≫ g = f := by
  classical
  let a (p q : ℕ) (_h : p + q = n) : B ⟶ (K.X p).X q :=
    if hq : q = 0 then 0 else (hf p q _h hq).choose
  let z := TotalComponentLift.lift K n a
  have hz : z ≫ projection K n = 0 := by
    rw [show z ≫ projection K n = a n 0 (by omega) from
      TotalComponentLift.lift_projection K n a n 0 (by omega)]
    simp only [a, dite_eq_left rfl]
  refine ⟨kernel.lift (projection K n) z hz, ?_⟩
  apply (cancel_mono (kernel.ι (projection K n))).mp
  rw [Category.assoc, kernel.lift_ι]
  apply AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatCoordinates.Projective.totalUpNat_hom_ext K n
  intro i
  rw [Category.assoc, TotalComponentLift.lift_projection K n a i (n-i) (by omega)]
  rw [Category.assoc]
  by_cases hq : n - (i : ℕ) = 0
  · have hi : (i : ℕ) = n := by omega
    simp only [a, dite_eq_left hq, comp_zero]
    change 0 = f ≫ kernel.ι (projection K n) ≫ (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (n - i) n
    rw [hi, Nat.sub_self, kernel.condition, comp_zero]
  · simpa only [a, dite_eq_right hq] using (hf i (n - i) (by omega) hq).choose_spec

theorem rows (S : CochainComplex C ℕ)
    (hK : ∀ p q, q ≠ 0 → Cochain.HomAcyclic.Rows S ((K.X p).X q)) :
    Cochain.HomAcyclic.Rows S (kernel (projection K n)) := by
  constructor
  · intro f
    apply factor K n (S.d 0 1) f
    intro p q _h hq
    exact (hK p q hq).zero _
  · intro i f hf
    apply factor K n (S.d (i + 1) (i + 2)) f
    intro p q _h hq
    apply (hK p q hq).succ i
    rw [← Category.assoc, ← Category.assoc, hf, zero_comp, zero_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TotalKernelHomRows
