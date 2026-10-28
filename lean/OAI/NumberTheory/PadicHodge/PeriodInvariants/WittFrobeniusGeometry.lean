import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

/-! # Witt Frobenius Geometry -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry

noncomputable section

/-!
# Absolute Frobenius over the Witt-vector base

The actual p-power Frobenius on a characteristic-p scheme lies over Witt
Frobenius. Both Witt Frobenius and its inverse preserve the canonical
divided powers, supplying the base automorphism for crystalline pullback.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

theorem inverse_mem (x : W) (hx : x ∈ Ideal.span {(p : W)}) :
    (φ).symm x ∈ Ideal.span {(p : W)} := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [map_mul, map_natCast]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)

theorem inverse_isDPMorphism : DividedPowers.IsDPMorphism γ γ (φ).symm.toRingHom where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun x hx => inverse_mem p k x hx)
  dpow_comp {n} x hx := by
    apply (φ).injective
    change φ ((γ).dpow n ((φ).symm x)) = φ ((φ).symm ((γ).dpow n x))
    rw [AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.frobenius_dpow p k n _ (inverse_mem p k x hx), (φ).apply_symm_apply,
      (φ).apply_symm_apply]

omit [PerfectRing k p] in
theorem absoluteFrobenius_spec :
    AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p (Fact.out : p.Prime) (Spec (CommRingCat.of k))
      (IntegralComparison.Global.FrobeniusGeometry.spec_prime_zero p k) = Spec.map (CommRingCat.ofHom (frobenius k p)) := by
  apply IntegralComparison.Global.FrobeniusGeometry.hom_ext_appTop
  apply (CategoryTheory.cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom).mp
  rw [Scheme.ΓSpecIso_naturality]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (s ^ p) =
    ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom s) ^ p
  exact map_pow _ s p

def schemeFrobenius (X : Over (Spec (CommRingCat.of k))) : X.left ⟶ X.left :=
  AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius p (Fact.out : p.Prime) X.left (IntegralComparison.Global.FrobeniusGeometry.scheme_prime_zero p k X.hom)

theorem schemeFrobenius_over (X : Over (Spec (CommRingCat.of k))) :
    schemeFrobenius p k X ≫ IntegralComparison.Witt.Crystalline.wittStructureMap p k X =
      IntegralComparison.Witt.Crystalline.wittStructureMap p k X ≫ Spec.map (CommRingCat.ofHom (φ).toRingHom) := by
  have hn := AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p (Fact.out : p.Prime)
    (IntegralComparison.Global.FrobeniusGeometry.scheme_prime_zero p k X.hom) (IntegralComparison.Global.FrobeniusGeometry.spec_prime_zero p k) X.hom
  change schemeFrobenius p k X ≫ X.hom = _ at hn
  rw [absoluteFrobenius_spec p k] at hn
  change schemeFrobenius p k X ≫ (X.hom ≫ Spec.map
      (CommRingCat.ofHom (WittVector.constantCoeff : W →+* k))) =
    (X.hom ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : W →+* k))) ≫ _
  rw [← Category.assoc, hn, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro w
  exact (WittVector.coeff_frobenius_charP p w 0).symm

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry
