import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalPositiveEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SeparatePolynomialMonomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ExternalSquareEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange

/-! # External Integer Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The external graph-bundle Euler monomial extends to arbitrary integer
powers of both factor classes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_external_integerClasses_euler
    (hN : 3 ≤ N) (hNk : (N : k) ≠ 0) (a b : ℤ) :
    LineBundle.EulerShifts.lineBundleClassEuler (A.abelian.scheme ⊗ A.abelian.scheme).hom
      (Line.Bundles.LineBundle.classOf (A.graphBundle.pullback (fst A.abelian.scheme A.abelian.scheme).left) ^ a *
        Line.Bundles.LineBundle.classOf (A.graphBundle.pullback (snd A.abelian.scheme A.abelian.scheme).left) ^ b) =
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2 * a ^ g * b ^ g := by
  let p := (A.abelian.scheme ⊗ A.abelian.scheme).hom
  let L := A.graphBundle.pullback (fst A.abelian.scheme A.abelian.scheme).left
  let M := A.graphBundle.pullback (snd A.abelian.scheme A.abelian.scheme).left
  have : IsProper p := inferInstanceAs
    (IsProper (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  have : Flat p := inferInstanceAs
    (Flat (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  have : LocallyOfFinitePresentation p := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  let E := Ample.ExternalSquareEmbedding.ampleExternalSquarePowerEmbedding A.graphBundle A.graphBundle_isAmple_overField
  let F : ℤ → ℤ → ℚ := fun a b =>
    (LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf L ^ a * Line.Bundles.LineBundle.classOf M ^ b) : ℚ)
  let c : ℤ := (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2
  have hfirst (b : ℤ) : ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p L (Line.Bundles.LineBundle.classOf M ^ b)
    exact ⟨P, fun a => by simpa only [F, mul_comm] using hP a⟩
  have hsecond (a : ℤ) : ∃ P : Polynomial ℚ, ∀ b : ℤ, P.eval (b : ℚ) = F a b :=
    E.lineBundleClass_integerEulerPolynomial p M (Line.Bundles.LineBundle.classOf L ^ a)
  have hpos (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      F m n = (c : ℚ) * (m : ℚ) ^ g * (n : ℚ) ^ g := by
    let e : (Line.Bundles.LineBundle.externalTensor A.abelian.scheme.hom A.abelian.scheme.hom
        (A.graphBundle.tensorPower m) (A.graphBundle.tensorPower n)).sheaf ≅
      ((L.tensorPower m).tensor (M.tensorPower n)).sheaf :=
      Tensor.Bifunctor.tensorModuleMapIso
        (A.graphBundle.powerBaseChangeIso (fst A.abelian.scheme A.abelian.scheme).left m)
        (A.graphBundle.powerBaseChangeIso (snd A.abelian.scheme A.abelian.scheme).left n)
    have he := Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p e
    have hv := A.graphBundle_external_positivePowers_euler hN hNk m n hm hn
    dsimp only [F]
    simp only [zpow_natCast, ← Line.Bundles.LineBundle.classOf_tensorPower, ← Line.Bundles.LineBundle.classOf_tensor,
      LineBundle.EulerShifts.lineBundleClassEuler_classOf]
    rw [← he]
    erw [hv]
    simp only [c, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have h := SeparatePolynomialMonomial.separately_polynomial_monomial_of_positive_grid F g (c : ℚ) hfirst hsecond hpos a b
  apply Int.cast_injective (α := ℚ)
  simpa only [F, c, Int.cast_mul, Int.cast_pow] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
