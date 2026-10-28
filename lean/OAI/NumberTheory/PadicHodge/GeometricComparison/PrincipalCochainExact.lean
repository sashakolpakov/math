import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PowerModuleSequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-! # Principal Cochain Exact -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient

noncomputable section

/-! The actual coefficient-power quotient sequence of a regular cochain complex and its connecting maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable (R : Type u) [CommRing R] (C : CochainComplex (ModuleCat.{v} R) ℕ) (r : R)

abbrev quotient (n : ℕ) := IntegralComparison.Module.IdealQuotient.complex R ((Ideal.span {r}) ^ n) C
abbrev projection (n : ℕ) := IntegralComparison.Module.IdealQuotient.complexProjection R ((Ideal.span {r}) ^ n) C

theorem scalar_projection (n : ℕ) : (r ^ n • 𝟙 C) ≫ projection R C r n = 0 := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Submodule.Quotient.mk (r ^ n • x) :
    IntegralComparison.Principal.PowerModuleSequence.Quotient R (C.X a) r n) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((IntegralComparison.Principal.PowerModuleSequence.mem_submodule R (C.X a) r n _).mpr ⟨x, rfl⟩)

def sequence (n : ℕ) : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk (r ^ n • 𝟙 C) (projection R C r n) (scalar_projection R C r n)

theorem shortExact (hreg : ∀ a, IsSMulRegular (C.X a) r) (n : ℕ) :
    (sequence R C r n).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro a
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have hx' : x ∈ IntegralComparison.Principal.PowerModuleSequence.submodule R (C.X a) r n :=
      (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := (IntegralComparison.Principal.PowerModuleSequence.mem_submodule R (C.X a) r n x).mp hx'
    exact ⟨y, hy⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact IsSMulRegular.pow n (hreg a)
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact (IntegralComparison.Principal.PowerModuleSequence.submodule R (C.X a) r n).mkQ_surjective

def transition (n m : ℕ) (h : n ≤ m) : quotient R C r m ⟶ quotient R C r n where
  f a := ModuleCat.ofHom (Submodule.factorPow (Ideal.span {r}) (C.X a) h)
  comm' a b _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (IntegralComparison.Principal.PowerModuleSequence.submodule R (C.X a) r m).mkQ_surjective x
    rfl

theorem projection_transition (n m : ℕ) (h : n ≤ m) :
    projection R C r m ≫ transition R C r n m h = projection R C r n := by
  apply HomologicalComplex.Hom.ext
  funext a
  rfl

def adjacent (n : ℕ) : sequence R C r (n + 1) ⟶ sequence R C r n where
  τ₁ := r • 𝟙 C
  τ₂ := 𝟙 C
  τ₃ := transition R C r n (n + 1) (Nat.le_succ n)
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext a
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change r ^ n • (r • x) = r ^ (n + 1) • x
    rw [← mul_smul, pow_succ]
  comm₂₃ := by
    change 𝟙 C ≫ projection R C r n = projection R C r (n + 1) ≫ _
    rw [Category.id_comp, projection_transition]

variable (hreg : ∀ a, IsSMulRegular (C.X a) r)

def connecting (n i : ℕ) : (quotient R C r n).homology i →ₗ[R] C.homology (i + 1) :=
  ((shortExact R C r hreg n).δ i (i + 1) rfl).hom

theorem homology_scalar (a : R) (i : ℕ) :
    HomologicalComplex.homologyMap (a • 𝟙 C) i = a • 𝟙 (C.homology i) := by
  change ShortComplex.homologyMap (a • 𝟙 (C.sc i)) = _
  rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

theorem connecting_torsion (n i : ℕ) (x : (quotient R C r n).homology i) :
    r ^ n • connecting R C r hreg n i x = 0 := by
  have h := (shortExact R C r hreg n).δ_comp i (i + 1) rfl
  change _ ≫ HomologicalComplex.homologyMap (r ^ n • 𝟙 C) (i + 1) = 0 at h
  rw [homology_scalar] at h
  exact ConcreteCategory.congr_hom h x

theorem connecting_transition (n i : ℕ) (x : (quotient R C r (n + 1)).homology i) :
    r • connecting R C r hreg (n + 1) i x = connecting R C r hreg n i
      (HomologicalComplex.homologyMap (transition R C r n (n + 1) (Nat.le_succ n)) i x) := by
  have h := HomologicalComplex.HomologySequence.δ_naturality (adjacent R C r n)
    (shortExact R C r hreg (n + 1)) (shortExact R C r hreg n) i (i + 1) rfl
  change _ ≫ HomologicalComplex.homologyMap (r • 𝟙 C) (i + 1) = _ at h
  rw [homology_scalar] at h
  exact ConcreteCategory.congr_hom h x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalCochainExact.PrincipalCochainQuotient
