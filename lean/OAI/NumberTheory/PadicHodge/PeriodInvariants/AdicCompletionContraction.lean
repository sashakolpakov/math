import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionLinear
import OAI.NumberTheory.PadicHodge.PeriodInvariants.ScalarNullhomotopyEta

/-! # Adic Completion Contraction -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionContraction

noncomputable section

/-! # Scalar contractions extend through adic completion of actual complexes -/

open _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (C : CochainComplex (ModuleCat.{u} R) ℕ)

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((AdicCompletionLinear.functor I).mapHomologicalComplex (.up ℕ)).obj C

variable (h : ∀ n, C.X (n + 1) →ₗ[R] C.X n) (a : R)
  (hzero : ∀ x, h 0 ((C.d 0 1).hom x) = a • x)
  (hsucc : ∀ n x, h (n + 1) ((C.d (n + 1) (n + 1 + 1)).hom x) +
    (C.d n (n + 1)).hom (h n x) = a • x)

def contraction (n : ℕ) : (complex I C).X (n + 1) →ₗ[R] (complex I C).X n :=
  AdicCompletionLinear.map I (h n)

include hzero in
theorem contraction_zero (x : (complex I C).X 0) :
    contraction I C h 0 (((complex I C).d 0 1).hom x) = a • x := by
  have he : (h 0).comp (C.d 0 1).hom = a • LinearMap.id := LinearMap.ext hzero
  have hc := congrArg (AdicCompletionLinear.map I) he
  rw [← AdicCompletionLinear.map_comp, AdicCompletionLinear.map_smul,
    AdicCompletionLinear.map_id] at hc
  exact LinearMap.congr_fun hc x

include hsucc in
theorem contraction_succ (n : ℕ) (x : (complex I C).X (n + 1)) :
    contraction I C h (n + 1) (((complex I C).d (n + 1) (n + 1 + 1)).hom x) +
      ((complex I C).d n (n + 1)).hom (contraction I C h n x) = a • x := by
  have he : (h (n + 1)).comp (C.d (n + 1) (n + 1 + 1)).hom + (C.d n (n + 1)).hom.comp (h n) =
      a • LinearMap.id := LinearMap.ext (hsucc n)
  have hc := congrArg (AdicCompletionLinear.map I) he
  rw [AdicCompletionLinear.map_add, ← AdicCompletionLinear.map_comp,
    ← AdicCompletionLinear.map_comp, AdicCompletionLinear.map_smul,
    AdicCompletionLinear.map_id] at hc
  exact LinearMap.congr_fun hc x

include hzero hsucc in
theorem eta_homology_subsingleton (ha : ∀ n, IsSMulRegular ((complex I C).X n) a) (n : ℕ) :
    Subsingleton ((EtaComplex.eta a (complex I C)).homology n) :=
  ScalarNullhomotopyEta.homology_subsingleton a (complex I C) (contraction I C h)
    (contraction_zero I C h a hzero) (contraction_succ I C h a hsucc) ha n

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicCompletionContraction
