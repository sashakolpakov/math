import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ExactPieces

/-! # Homology -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Homology

noncomputable section

/-! The Bockstein short exact sequence for homology of a complex
whose terms have no parameter torsion. All maps come from the native
homology sequence of multiplication by the parameter. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.QuotientComplex

variable (R : Type u) [CommRing R] (r : R)
  (K : ChainComplex (ModuleCat.{u} R) ℕ)
  (hr : ∀ i, IsSMulRegular (K.X i) r)

def reduction (i : ℕ) : K.homology i ⟶ (QuotientComplex.complex R r K).homology i :=
  HomologicalComplex.homologyMap (QuotientComplex.projection R r K) i

theorem scalar_hom (M : ModuleCat.{u} R) :
    (r • 𝟙 M).hom = LinearMap.lsmul R M r := by
  apply LinearMap.ext
  intro x
  simp

include hr

theorem exact_scalar_reduction (i : ℕ) :
    Function.Exact (LinearMap.lsmul R (K.homology i) r) (reduction R r K i).hom := by
  have h := (QuotientComplex.shortExact R r K hr).homology_exact₂ i
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  rw [← scalar_hom R r (K.homology i), ← QuotientComplex.homology_scalar R r K i]
  exact h

theorem exact_reduction_connecting (i : ℕ) :
    Function.Exact (reduction R r K (i + 1)).hom (QuotientComplex.connecting R r K hr i).hom := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((QuotientComplex.shortExact R r K hr).homology_exact₃ (i + 1) i (by simp))

theorem exact_connecting_scalar (i : ℕ) :
    Function.Exact (QuotientComplex.connecting R r K hr i).hom (LinearMap.lsmul R (K.homology i) r) := by
  have h := (QuotientComplex.shortExact R r K hr).homology_exact₁ (i + 1) i (by simp)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  rw [← scalar_hom R r (K.homology i), ← QuotientComplex.homology_scalar R r K i]
  exact h

def sequence (i : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ExactPieces.sequence R r (K.homology (i + 1))
    ((QuotientComplex.complex R r K).homology (i + 1)) (K.homology i)
    (reduction R r K (i + 1)).hom (QuotientComplex.connecting R r K hr i).hom
    (exact_scalar_reduction R r K hr (i + 1))
    (exact_reduction_connecting R r K hr i) (exact_connecting_scalar R r K hr i)

theorem sequence_shortExact (i : ℕ) : (sequence R r K hr i).ShortExact :=
  ExactPieces.shortExact R r _ _ _ _ _ _ _ _

theorem reduction_zero_surjective : Function.Surjective (reduction R r K 0) := by
  let : Epi (QuotientComplex.projection R r K) := (QuotientComplex.shortExact R r K hr).epi_g
  let : Epi (HomologicalComplex.homologyMap (QuotientComplex.projection R r K) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (QuotientComplex.projection R r K) 0 (by simp)
  exact (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap (QuotientComplex.projection R r K) 0)).mp inferInstance

def zeroEquiv : QuotSMulTop r (K.homology 0) ≃ₗ[R] (QuotientComplex.complex R r K).homology 0 :=
  LinearEquiv.ofBijective
    (ExactPieces.left R r _ _ (reduction R r K 0).hom
      (exact_scalar_reduction R r K hr 0))
    ⟨ExactPieces.left_injective R r _ _ _ _, by
      intro b
      obtain ⟨a, ha⟩ := reduction_zero_surjective R r K hr b
      exact ⟨Submodule.Quotient.mk a, ha⟩⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Homology
