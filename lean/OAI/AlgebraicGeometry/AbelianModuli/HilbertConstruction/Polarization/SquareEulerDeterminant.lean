import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EulerSquareNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerDeterminant

/-! # Square Euler Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The determinant formula applies to actual polarization bundle classes
on the square. The normalized polarization isomorphism supplies the shear
law, and genuine external-product cohomology supplies the diagonal values. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.polarizationSquareClass_euler_determinant_of_normalized_formula
    (hN : 3 ≤ N) (hNk : (N : k) ≠ 0)
    (L : Line.Bundles.LineBundle A.abelian.scheme.left)
    (e : (((A.dual.poincareAt A.polarization.isogeny.hom).tensor
      (L.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
        (L.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
      (L.pullback μ[A.abelian.scheme].left).sheaf)
    (a b c : ℤ) :
    (4 : ℚ) ^ g * (LineBundle.EulerShifts.lineBundleClassEuler (A.abelian.scheme ⊗ A.abelian.scheme).hom
      (Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom a b c) : ℚ) =
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ) ^ 2 *
      (4 * (a : ℚ) * (b : ℚ) - (c : ℚ) ^ 2) ^ g := by
  let p := (A.abelian.scheme ⊗ A.abelian.scheme).hom
  let : IsProper p := inferInstanceAs
    (IsProper (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  let : Flat p := inferInstanceAs
    (Flat (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  let : LocallyOfFinitePresentation p := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  let : (A.abelian.scheme ⊗ A.abelian.scheme).left.IsSeparated := by
    constructor
    rw [← terminal.comp_from p]
    infer_instance
  let E := Ample.ExternalSquareEmbedding.ampleExternalSquarePowerEmbedding A.graphBundle A.graphBundle_isAmple_overField
  let B : Line.Bundles.LineBundle (A.abelian.scheme ⊗ A.abelian.scheme).left :=
    A.dual.poincareAt A.polarization.isogeny.hom
  let L₁ := A.graphBundle.pullback (fst A.abelian.scheme A.abelian.scheme).left
  let L₂ := A.graphBundle.pullback (snd A.abelian.scheme A.abelian.scheme).left
  let F : ℤ → ℤ → ℤ → ℚ := fun a b c =>
    (LineBundle.EulerShifts.lineBundleClassEuler p (Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom a b c) : ℚ)
  let d : ℚ := (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ) ^ 2
  have hA (b c : ℤ) : ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b c := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p L₁
      (Line.Bundles.LineBundle.classOf L₂ ^ b * Line.Bundles.LineBundle.classOf B ^ c)
    refine ⟨P, fun a => ?_⟩
    have he : (Line.Bundles.LineBundle.classOf L₂ ^ b * Line.Bundles.LineBundle.classOf B ^ c) * Line.Bundles.LineBundle.classOf L₁ ^ a =
        Line.Bundles.LineBundle.classOf L₁ ^ a * Line.Bundles.LineBundle.classOf L₂ ^ b * Line.Bundles.LineBundle.classOf B ^ c :=
      (mul_comm _ _).trans (mul_assoc _ _ _).symm
    have h := (hP a).trans (congrArg (fun z : Line.Bundles.LineBundle.IsoClass (A.abelian.scheme ⊗ A.abelian.scheme).left =>
      (LineBundle.EulerShifts.lineBundleClassEuler p z : ℚ)) he)
    dsimp only [F]
    rw [Polarization.ShearClasses.polarizationSquareClass_as_bundles]
    exact h
  have hC (a b : ℤ) : ∃ P : Polynomial ℚ, ∀ c : ℤ, P.eval (c : ℚ) = F a b c := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p B
      (Line.Bundles.LineBundle.classOf L₁ ^ a * Line.Bundles.LineBundle.classOf L₂ ^ b)
    refine ⟨P, fun c => ?_⟩
    dsimp only [F]
    rw [Polarization.ShearClasses.polarizationSquareClass_as_bundles]
    exact hP c
  have hshear (a b c t : ℤ) : F a b c = F a (b + t * c + t ^ 2 * a) (c + 2 * t * a) := by
    have h := LineBundle.ClassEulerIsomorphism.lineBundleClassEuler_pullback_overIso (Product.ShearIsomorphisms.productShearIso A.abelian.scheme t)
      (Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom a b c)
    rw [Polarization.ShearClasses.polarizationSquareClass_pullback_shear A.dual A.polarization.isogeny.hom L e] at h
    exact congrArg (fun z : ℤ => (z : ℚ)) h.symm
  have hdiag (a b : ℤ) : F a b 0 = d * (a : ℚ) ^ g * (b : ℚ) ^ g := by
    dsimp only [F]
    rw [Polarization.ShearClasses.polarizationSquareClass_as_bundles, zpow_zero, mul_one]
    have h := A.graphBundle_external_integerClasses_euler hN hNk a b
    have hq : (LineBundle.EulerShifts.lineBundleClassEuler (A.abelian.scheme ⊗ A.abelian.scheme).hom
        (Line.Bundles.LineBundle.classOf L₁ ^ a * Line.Bundles.LineBundle.classOf L₂ ^ b) : ℚ) =
        (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ) ^ 2 *
          (a : ℚ) ^ g * (b : ℚ) ^ g := by
      exact_mod_cast h
    exact hq
  exact ShearEulerDeterminant.shear_euler_determinant_formula F g d hA hC hshear hdiag a b c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
