import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex

/-! # Eta Cycles -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles

noncomputable section

/-!
# Cycles of the eta complex

For termwise a-torsion-free complexes, multiplication by a^n identifies
the original cycles in degree n with the cycles of the eta complex.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaComplex

variable {R : Type u} [CommRing R] (a : R)

def cycles (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) : Submodule R (C.X n) :=
  LinearMap.ker (C.d n (n + 1)).hom

def etaCycles (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    Submodule R (EtaComplex.term a C n) := LinearMap.ker (EtaComplex.differential a C n)

def scaledTerm (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    cycles C n →ₗ[R] EtaComplex.term a C n where
  toFun x := ⟨a ^ n • (x : C.X n), (EtaComplex.mem_term a C n _).mpr
    ⟨⟨x, rfl⟩, ⟨0, by
      have hx : C.d n (n + 1) x = 0 := x.property
      rw [map_smul, hx, smul_zero, smul_zero]⟩⟩⟩
  map_add' x y := Subtype.ext (smul_add (a ^ n) (x : C.X n) (y : C.X n))
  map_smul' r x := Subtype.ext (smul_comm (a ^ n) r (x : C.X n))

theorem scaledTerm_cycle (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : cycles C n) :
    EtaComplex.differential a C n (scaledTerm a C n x) = 0 := by
  apply Subtype.ext
  change C.d n (n + 1) (a ^ n • (x : C.X n)) = 0
  have hx : C.d n (n + 1) x = 0 := x.property
  rw [map_smul, hx, smul_zero]

def scaleCycles (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    cycles C n →ₗ[R] etaCycles a C n :=
  (scaledTerm a C n).codRestrict _ (scaledTerm_cycle a C n)

theorem scaleCycles_injective (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X n) a) : Function.Injective (scaleCycles a C n) := by
  intro x y h
  apply Subtype.ext
  apply ha.pow n
  exact congrArg (fun z : etaCycles a C n => (z.val : C.X n)) h

theorem scaleCycles_surjective (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X (n + 1)) a) : Function.Surjective (scaleCycles a C n) := by
  intro x
  obtain ⟨⟨y, hy⟩, _⟩ := (EtaComplex.mem_term a C n x.val).mp x.val.property
  have hx : C.d n (n + 1) (x.val : C.X n) = 0 :=
    congrArg (fun z : EtaComplex.term a C (n + 1) => (z : C.X (n + 1)))
      (show EtaComplex.differential a C n x.val = 0 from x.property)
  have hycycle : C.d n (n + 1) y = 0 := by
    apply ha.pow n
    change a ^ n • C.d n (n + 1) y = a ^ n • (0 : C.X (n + 1))
    rw [smul_zero, ← map_smul, hy]
    exact hx
  refine ⟨⟨y, hycycle⟩, ?_⟩
  apply Subtype.ext
  exact Subtype.ext hy

def cyclesEquiv (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X n) a) (ha' : IsSMulRegular (C.X (n + 1)) a) :
    cycles C n ≃ₗ[R] etaCycles a C n :=
  LinearEquiv.ofBijective (scaleCycles a C n)
    ⟨scaleCycles_injective a C n ha, scaleCycles_surjective a C n ha'⟩

theorem cyclesEquiv_apply (C : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (ha : IsSMulRegular (C.X n) a) (ha' : IsSMulRegular (C.X (n + 1)) a)
    (x : cycles C n) :
    ((cyclesEquiv a C n ha ha' x).val : C.X n) = a ^ n • (x : C.X n) := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaCycles
