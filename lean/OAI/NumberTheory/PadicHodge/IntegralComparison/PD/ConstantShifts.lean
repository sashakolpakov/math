import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham

/-! # Constant Shifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.ConstantShifts

noncomputable section

/-!
# IntegralComparison: relative differential symbols ignore shifts by coefficient constants

The defining differential relations kill base-ring constants in each
slot. Simultaneous changes of coordinate lifts therefore leave the
actual relative divided-power differential symbol unchanged.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I)

theorem symbol_update_add_base {n : ℕ} (c : A) (v : Fin n → A) (i : Fin n) (z : A) (a : R) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (Function.update v i (z + algebraMap R A a)) =
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (Function.update v i z) := by
  calc
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (Function.update v i (z + algebraMap R A a)) =
        c • AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i (z + algebraMap R A a)) :=
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ c _
    _ = c • AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ 1 (Function.update v i z) := by
      congr 1
      unfold AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol
      rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_add, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_update_base, add_zero]
    _ = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (Function.update v i z) :=
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol_smul_one R A I δ c _).symm

theorem symbol_shift {n : ℕ} (c : A) (v : Fin n → A) (a : Fin n → R) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (fun i => v i + algebraMap R A (a i)) = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c v := by
  classical
  have hs (s : Finset (Fin n)) :
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (fun i => if i ∈ s then v i + algebraMap R A (a i) else v i) =
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c v := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, ↓reduceIte]
    | @insert i s hi ih =>
      have hvec : (fun j => if j ∈ insert i s then v j + algebraMap R A (a j) else v j) =
          Function.update (fun j => if j ∈ s then v j + algebraMap R A (a j) else v j)
            i (v i + algebraMap R A (a i)) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [Finset.mem_insert, hji]
      have hrestore : Function.update
          (fun j => if j ∈ s then v j + algebraMap R A (a j) else v j) i (v i) =
            (fun j => if j ∈ s then v j + algebraMap R A (a j) else v j) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [hi]
        · simp [Function.update_of_ne hji]
      rw [hvec, symbol_update_add_base, hrestore]
      exact ih
  simpa only [Finset.mem_univ, ↓reduceIte] using hs Finset.univ

theorem symbol_base_add {n : ℕ} (c : A) (v : Fin n → A) (a : Fin n → R) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c (fun i => algebraMap R A (a i) + v i) = AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R A I δ c v := by
  simpa only [add_comm] using symbol_shift R A I δ c v a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.ConstantShifts
