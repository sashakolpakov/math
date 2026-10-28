import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBiproduct
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Flasque Bounded Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBoundedExactness

noncomputable section

/-! Exact open sections of bounded-below, integer-indexed flasque complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open _root_.CategoryTheory.Preadditive

theorem int_prev (n : ℤ) : (ComplexShape.up ℤ).prev n = n - 1 :=
  (ComplexShape.up ℤ).prev_eq' (show (n - 1) + 1 = n by omega)

section Successors

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ) (n : ℤ)

abbrev intSuccessorSequence : ShortComplex C :=
  ShortComplex.mk (K.fromOpcycles n (n + 1)) (K.pOpcycles (n + 1)) (by
    rw [← cancel_epi (K.pOpcycles n), comp_zero,
      HomologicalComplex.p_fromOpcycles_assoc, HomologicalComplex.d_pOpcycles])

theorem intSuccessorSequence_exact : (intSuccessorSequence K n).Exact := by
  let S := ShortComplex.mk (K.d n (n + 1)) (K.pOpcycles (n + 1)) (K.d_pOpcycles n (n + 1))
  have hS : S.Exact := S.exact_of_g_is_cokernel (K.opcyclesIsCokernel n (n + 1) (by simp))
  let φ : S ⟶ intSuccessorSequence K n :=
    { τ₁ := K.pOpcycles n
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, intSuccessorSequence]
      comm₂₃ := by simp [S, intSuccessorSequence] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS

theorem intSuccessorSequence_shortExact (h : K.ExactAt n) :
    (intSuccessorSequence K n).ShortExact := by
  have hm : Mono (K.fromOpcycles n (n + 1)) :=
    mono_of_isZero_kernel' _ (K.homologyIsKernel n (n + 1) (by simp)) h.isZero_homology
  exact ShortComplex.ShortExact.mk' (intSuccessorSequence_exact K n) hm inferInstance

end Successors

variable {X : TopCat.{0}} (K : CochainComplex (FlasqueBiproduct.ComplexSheaves X) ℤ)
  (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (hacyclic : K.Acyclic)
  (d : ℤ) (hbound : ∀ n, n < d → IsZero (K.X n))

include hK hacyclic hbound

theorem int_opcycles_flasque (k : ℕ) : TopCat.Sheaf.IsFlasque (K.opcycles (d + k)) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    have hz : K.d (d - 1) d = 0 := (hbound (d - 1) (by omega)).eq_of_src _ _
    have := hK d
    exact FlasqueBiproduct.flasque_of_iso (K.pOpcyclesIso (d - 1) d (int_prev d) hz)
  | succ k ih =>
    have := ih
    have := hK (d + k + 1)
    have h := Complex.SheafForget.Flasque.flasque_of_shortExact₁₂ (intSuccessorSequence K (d + k))
      (intSuccessorSequence_shortExact K (d + k) (hacyclic (d + k)))
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem int_sections_pOpcycles_epi (U : Opens X) (k : ℕ) :
    Epi ((FlasqueBiproduct.sections U).map (K.pOpcycles (d + k))) := by
  cases k with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    have : IsIso (K.pOpcycles d) :=
      K.isIso_pOpcycles (d - 1) d (int_prev d) ((hbound (d - 1) (by omega)).eq_of_src _ _)
    infer_instance
  | succ k =>
    have := int_opcycles_flasque K hK hacyclic d hbound k
    have h := (FlasqueBiproduct.sections_shortExact U (intSuccessorSequence K (d + k))
      (intSuccessorSequence_shortExact K (d + k) (hacyclic (d + k)))).epi_g
    rw [show d + ((k + 1 : ℕ) : ℤ) = (d + k) + 1 by omega]
    exact h

theorem int_sections_preserves_incoming_cokernel (U : Opens X) (k : ℕ) :
    PreservesColimit (parallelPair (K.sc (d + k)).f 0) (FlasqueBiproduct.sections U) := by
  cases k with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    apply preservesCokernel_zero'
    change K.d ((ComplexShape.up ℤ).prev d) d = 0
    rw [int_prev]
    exact (hbound (d - 1) (by omega)).eq_of_src _ _
  | succ k =>
    have heq : d + ((k + 1 : ℕ) : ℤ) = (d + k) + 1 := by omega
    rw [heq]
    change PreservesColimit (parallelPair (K.d ((ComplexShape.up ℤ).prev (d + k + 1))
      (d + k + 1)) 0) (FlasqueBiproduct.sections U)
    rw [show (ComplexShape.up ℤ).prev (d + k + 1) = d + k from by rw [int_prev]; omega]
    have := int_opcycles_flasque K hK hacyclic d hbound k
    have := int_sections_pOpcycles_epi K hK hacyclic d hbound U k
    let S := intSuccessorSequence K (d + k)
    have hS := FlasqueBiproduct.sections_shortExact U S (intSuccessorSequence_shortExact K (d + k) (hacyclic (d + k)))
    have := hS.epi_g
    refine preservesColimit_of_preserves_colimit_cocone
      (K.opcyclesIsCokernel (d + k) (d + k + 1) (by simp)) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ (FlasqueBiproduct.sections U)).2
    exact isCokernelEpiComp hS.exact.gIsCokernel ((FlasqueBiproduct.sections U).map (K.pOpcycles (d + k)))
      (hg := int_sections_pOpcycles_epi K hK hacyclic d hbound U k) (by
      change (FlasqueBiproduct.sections U).map (K.d (d + k) (d + k + 1)) =
        (FlasqueBiproduct.sections U).map (K.pOpcycles (d + k)) ≫ (FlasqueBiproduct.sections U).map (K.fromOpcycles (d + k) (d + k + 1))
      rw [← Functor.map_comp, HomologicalComplex.p_fromOpcycles])

/-- Exactness survives actual open sections for every bounded-below flasque complex. -/
theorem bounded_sections_acyclic (U : Opens X) :
    (((FlasqueBiproduct.sections U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro n
  by_cases hn : n < d
  · exact ShortComplex.exact_of_isZero_X₂ _ ((FlasqueBiproduct.sections U).map_isZero (hbound n hn))
  · let k := (n - d).toNat
    have heq : n = d + (k : ℤ) := by dsimp [k]; omega
    rw [heq]
    have := int_sections_preserves_incoming_cokernel K hK hacyclic d hbound U k
    have : (FlasqueBiproduct.sections U).PreservesRightHomologyOf (K.sc (d + k)) := by
      constructor
      intro h
      exact { f := inferInstance, g' := inferInstance }
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((FlasqueBiproduct.sections U).map_isZero (hacyclic (d + k)).isZero_homology).of_iso
      ((K.sc (d + k)).mapHomologyIso' (FlasqueBiproduct.sections U))

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueBoundedExactness
