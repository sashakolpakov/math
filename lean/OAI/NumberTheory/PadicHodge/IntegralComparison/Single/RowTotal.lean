import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyConcentration
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Row Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotal

noncomputable section

/-! The native total of a bicomplex supported in one row has the
cohomology of that row, with the actual degree shift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex

universe u v

variable {R : Type u} [CommRing R]
  (B : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
  (c : ℕ) (hB : ∀ p q, q ≠ c → IsZero ((B.X p).X q))

def componentIso (p : ℕ) : (B.X p).X c ≅ (B.total (.up ℕ)).X (p + c) where
  hom := B.ιTotal (.up ℕ) p c (p + c) rfl
  inv := AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.πTotal B p c (p + c) rfl
  hom_inv_id := AlgebraicTopology.DeRham.Comparison.DoubleComplexProjections.DoubleComplex.iota_πTotal_self B p c (p + c) rfl
  inv_hom_id := by
    apply HomologicalComplex₂.total.hom_ext
    intro a b hab
    by_cases hb : b = c
    · subst b
      have ha : a = p := by change a + c = p + c at hab; omega
      subst a
      simp
    · exact (hB a b hb).eq_of_src _ _

def restrictionIso : B.flip.X c ≅
    (B.total (.up ℕ)).restriction (CohomologyConcentration.shift c) :=
  HomologicalComplex.Hom.isoOfComponents (componentIso B c hB) (by
    intro p p' hp
    have hp' : p + 1 = p' := hp
    subst p'
    change B.ιTotal (.up ℕ) p c (p + c) rfl ≫
      (B.total (.up ℕ)).d (p + c) (p + 1 + c) =
        (B.d p (p + 1)).f c ≫ B.ιTotal (.up ℕ) (p + 1) c (p + 1 + c) rfl
    have hz : (B.X p).d c (c + 1) = 0 := (hB p (c + 1) (by omega)).eq_of_tgt _ _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      B.d₁_eq (.up ℕ) (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) c (p + 1 + c) rfl,
      B.d₂_eq (.up ℕ) p (show (ComplexShape.up ℕ).Rel c (c + 1) from rfl)
        (p + 1 + c) (by change p + (c + 1) = p + 1 + c; omega),
      hz, zero_comp, smul_zero, add_zero]
    simp only [AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex.epsilon1_upNat, one_smul])

include hB in
theorem supported : (B.total (.up ℕ)).IsStrictlySupported (CohomologyConcentration.shift c) := by
  constructor
  intro n hn
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have hq : q ≠ c := by
    intro hq
    apply hn p
    change p + c = n
    simpa only [hq] using hpq
  exact (hB p q hq).eq_of_src _ _

def homologyIso (n : ℕ) :
    (B.total (.up ℕ)).homology (n + c) ≅ (B.flip.X c).homology n := by
  let K := B.total (.up ℕ)
  let e := CohomologyConcentration.shift c
  have : K.IsStrictlySupported e := supported B c hB
  have : IsIso (K.restrictionToTruncGE' e) := HomologicalComplex.Hom.isIso_of_components _
  exact (HomologicalComplex.homologyMapIso (asIso (K.πTruncGE e)) (n + c)) ≪≫
    (K.truncGE' e).extendHomologyIso e rfl ≪≫
    (HomologicalComplex.homologyMapIso (asIso (K.restrictionToTruncGE' e)) n).symm ≪≫
    (HomologicalComplex.homologyMapIso (restrictionIso B c hB) n).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotal
