import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianDescent
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicHodgeMaps

/-! # Algebraic Enhancement -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicEnhancement.Abelian

noncomputable section

section

/-!
A finite enhancement by genuine algebraic endomorphisms at every CM point.
The rational CM operators are algebraized using the proved HolomorphicAlgebraicity theorem and
the supplied canonical Hodge structure. Multiplication by the resulting
positive denominators does not change the invariant-subspace condition.

This discharges the algebraic-endomorphism step in the enhanced-moduli
route. Existence of the enhanced arithmetic moduli scheme and its local
deformation comparison are separate geometric steps.
-/

open _root_.CategoryTheory

/-- The actual algebraic group endomorphisms used to enhance a CM point
are constructed, and their genuine H¹ pullbacks isolate its Hodge period
in the transverse graph chart. -/
theorem hasCMH1_finite_algebraic_enhancement_rigid
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1) :
    ∃ (r : ℕ) (g : Fin r → (A.toOver ⟶ A.toOver)),
      (∀ i, IsMonHom (g i)) ∧
      (∀ i x, x ∈ A.h1Holomorphic →
        (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (g i)).baseChange ℂ x ∈ A.h1Holomorphic) ∧
      (∀ i x, x ∈ A.h1Antiholomorphic →
        (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (g i)).baseChange ℂ x ∈ A.h1Antiholomorphic) ∧
      ∀ W : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)),
        IsCompl W A.h1Antiholomorphic →
        (∀ i x, x ∈ W → (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (g i)).baseChange ℂ x ∈ W) →
        W = A.h1Holomorphic := by
  obtain ⟨r, f, hfh, hfa, hrigid⟩ := AbelianDescent.hasCMH1_finite_rational_enhancement_rigid A hCM
  obtain ⟨H, hhol, hanti, _⟩ := hCM
  have hf (i : Fin r) : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (f i) := by
    intro x hx
    rw [hhol] at hx ⊢
    exact hfh i x hx
  have hcan : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 A.variety H := ⟨hhol, hanti⟩
  choose n hn g hg hpull using
    fun i => IntrinsicHodgeMaps.Abelian.hodge_map_algebraic_of_canonicalH1 A A H H hcan hcan (f i) (hf i)
  refine ⟨r, g, hg, ?_, ?_, ?_⟩
  · intro i x hx
    rw [hpull, LinearMap.baseChange_smul, LinearMap.smul_apply]
    exact Submodule.smul_of_tower_mem _ _ (hfh i x hx)
  · intro i x hx
    rw [hpull, LinearMap.baseChange_smul, LinearMap.smul_apply]
    exact Submodule.smul_of_tower_mem _ _ (hfa i x hx)
  · intro W hW hInv
    apply hrigid W hW
    intro i x hx
    have hmem := hInv i x hx
    rw [hpull, LinearMap.baseChange_smul, LinearMap.smul_apply] at hmem
    have hnq : (n i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hn i))
    have he : (n i : ℚ)⁻¹ • ((n i : ℚ) • (f i).baseChange ℂ x) =
        (f i).baseChange ℂ x := by
      rw [smul_smul, inv_mul_cancel₀ hnq, one_smul]
    rw [← he]
    exact Submodule.smul_of_tower_mem _ _ hmem

end

/-!
The finite CM enhancement as explicit data, chosen before any family or
period chart. Its linear rigidity is proved from the original CM
hypothesis, so the same tuple can be spread and used in every family.
-/

open _root_.CategoryTheory

structure CMEnhancement (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) where
  size : ℕ
  map : Fin size → (A.toOver ⟶ A.toOver)
  group : ∀ i, IsMonHom (map i)
  rigid : ∀ W : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (A.variety.rationalCohomology 1)),
    IsCompl W A.h1Antiholomorphic →
    (∀ i x, x ∈ W → (AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback (map i)).baseChange ℂ x ∈ W) →
    W = A.h1Holomorphic

attribute [instance] CMEnhancement.group

theorem cmEnhancement_nonempty (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1) :
    Nonempty (CMEnhancement A) := by
  obtain ⟨r, m, hm, _, _, hr⟩ := hasCMH1_finite_algebraic_enhancement_rigid A hCM
  exact ⟨⟨r, m, hm, hr⟩⟩

def CMEnhancement.ofHasCM (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (hCM : A.HasCMH1) : CMEnhancement A :=
  Classical.choice (cmEnhancement_nonempty A hCM)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AlgebraicEnhancement.Abelian
