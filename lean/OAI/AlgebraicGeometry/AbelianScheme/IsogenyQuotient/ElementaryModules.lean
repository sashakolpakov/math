import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.Products
import Mathlib.Algebra.Module.ZMod

/-! # Elementary Modules -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules.Construction

noncomputable section

/-!
The actual elementary-divisor modules for the three coordinates of each
chosen split block. The bounds a_i <= h provide their Z/(q^h)-module
structure. This specializes TorsionQuotient's module parameter to the stated integral
cocharacters rather than leaving the elementary type as an opaque input.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- The prescribed rank-three elementary group, with a harmless universe lift. -/
abbrev RankThreeElementaryModule (q : ℕ) (a : Fin 3 → ℕ) : Type u :=
  ULift.{u} (∀ i : Fin 3, ZMod (q ^ a i))

theorem rankThreeElementaryModule_killed
    (q h : ℕ) (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ h)
    (x : RankThreeElementaryModule.{u} q a) : (q ^ h) • x = 0 := by
  apply ULift.ext
  funext i
  change (q ^ h) • x.down i = 0
  rw [nsmul_eq_mul]
  have hz : ((q ^ h : ℕ) : ZMod (q ^ a i)) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod (q ^ a i)) (q ^ a i) (q ^ h)).mpr
      (pow_dvd_pow q (ha i))
  rw [hz, zero_mul]

abbrev rankThreeElementaryModule_structure
    (q h : ℕ) (a : Fin 3 → ℕ) (ha : ∀ i, a i ≤ h) :
    Module (ZMod (q ^ h)) (RankThreeElementaryModule.{u} q a) :=
  AddCommGroup.zmodModule (rankThreeElementaryModule_killed q h a ha)

instance rankThreeElementaryModule_finite
    (q : ℕ) [NeZero q] (a : Fin 3 → ℕ) :
    Finite (RankThreeElementaryModule.{u} q a) := by
  infer_instance

open scoped _root_.CategoryTheory.MonObj in
/-- Integral exponents with the single multiplier q^h have a finite etale
parameter scheme for all their chosen-block subgroups, over the given
characteristic-zero field. Only the exact repaired TorsionQuotient input is used. -/
theorem integral_block_parameters_from_TorsionQuotient
    {K : Type u} [Field K] [CharZero K] {S : Scheme.{u}}
    (base : S ⟶ Spec (CommRingCat.of K))
    (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (q : ℕ) (hq : q.Prime) (h s : ℕ)
    (a : Fin s → Fin 3 → ℕ) (ha : ∀ v i, a v i ≤ h)
    (projectorLift : Fin s → (A ⟶ A)) [∀ i, IsMonHom (projectorLift i)]
    (h_TorsionQuotient : Unit.Construction.TorsionQuotientInput.{u}) :
    letI : NeZero q := ⟨hq.ne_zero⟩
    letI : ∀ v, Module (ZMod (q ^ h)) (RankThreeElementaryModule.{u} q (a v)) :=
      fun v => rankThreeElementaryModule_structure q h (a v) (ha v)
    ∃ P : Over S,
      IsFinite P.hom ∧ Etale P.hom ∧
      Nonempty ((Parameter.Products.Construction.blockTupleFunctor s (fun v =>
        SubgroupFunctor.Construction.supportedSubgroupFunctor A (q ^ h)
          (RankThreeElementaryModule.{u} q (a v)) (projectorLift v))).RepresentableBy P) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let : ∀ v, Module (ZMod (q ^ h)) (RankThreeElementaryModule.{u} q (a v)) :=
    fun v => rankThreeElementaryModule_structure q h (a v) (ha v)
  exact Parameter.Products.Construction.chosen_block_parameters_from_TorsionQuotient base A (q ^ h) (pow_pos hq.pos h) s
    (fun v => RankThreeElementaryModule.{u} q (a v)) projectorLift h_TorsionQuotient

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryModules.Construction
