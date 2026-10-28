import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.ExternalIntegerEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ShearClasses
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassEulerIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BiextensionEuler

/-! # Euler Square Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The normalized polarization formula, integer shear identities, and the
computed Poincare Euler characteristic determine the square of the graph
Euler coefficient. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_euler_square_of_normalized_formula
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : k) ≠ 0)
    (L : Line.Bundles.LineBundle A.abelian.scheme.left)
    (e : (((A.dual.poincareAt A.polarization.isogeny.hom).tensor
      (L.pullback (fst A.abelian.scheme A.abelian.scheme).left)).tensor
        (L.pullback (snd A.abelian.scheme A.abelian.scheme).left)).sheaf ≅
      (L.pullback μ[A.abelian.scheme].left).sheaf) :
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2 =
      ((2 : ℤ) ^ g * ((∏ i, δ i : ℕ) : ℤ)) ^ 2 := by
  let p := (A.abelian.scheme ⊗ A.abelian.scheme).hom
  have : IsProper p := inferInstanceAs
    (IsProper (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  have : Flat p := inferInstanceAs
    (Flat (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  have : LocallyOfFinitePresentation p := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst A.abelian.scheme.hom A.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  have : (A.abelian.scheme ⊗ A.abelian.scheme).left.IsSeparated := by
    constructor
    rw [← terminal.comp_from p]
    infer_instance
  let E := Ample.ExternalSquareEmbedding.ampleExternalSquarePowerEmbedding A.graphBundle A.graphBundle_isAmple_overField
  let B : Line.Bundles.LineBundle (A.abelian.scheme ⊗ A.abelian.scheme).left :=
    A.dual.poincareAt A.polarization.isogeny.hom
  let L₁ := A.graphBundle.pullback (fst A.abelian.scheme A.abelian.scheme).left
  let F : ℤ → ℤ → ℤ → ℚ := fun a b c =>
    (LineBundle.EulerShifts.lineBundleClassEuler p (Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom a b c) : ℚ)
  let d : ℤ := (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf) ^ 2
  have hA (c : ℤ) : ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a 0 c := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p L₁ (Line.Bundles.LineBundle.classOf B ^ c)
    refine ⟨P, fun a => ?_⟩
    dsimp only [F]
    rw [Polarization.ShearClasses.polarizationSquareClass_as_bundles, zpow_zero, mul_one]
    change P.eval (a : ℚ) =
      (LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf L₁ ^ a * Line.Bundles.LineBundle.classOf B ^ c) : ℚ)
    exact (hP a).trans (congrArg (fun q : Line.Bundles.LineBundle.IsoClass
      (A.abelian.scheme ⊗ A.abelian.scheme).left => (LineBundle.EulerShifts.lineBundleClassEuler p q : ℚ))
        (mul_comm _ _))
  have hC : ∃ P : Polynomial ℚ, ∀ c : ℤ, P.eval (c : ℚ) = F 0 0 c := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p B 1
    refine ⟨P, fun c => ?_⟩
    simpa only [F, Polarization.ShearClasses.polarizationSquareClass_as_bundles, zpow_zero, one_mul, B] using hP c
  have hswap (a b c : ℤ) : F a b c = F b a c := by
    have h := LineBundle.ClassEulerIsomorphism.lineBundleClassEuler_pullback_overIso (Product.ShearIsomorphisms.productSwapIso A.abelian.scheme)
      (Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom a b c)
    rw [Polarization.ShearClasses.polarizationSquareClass_pullback_swap A.dual A.polarization.isogeny.hom L e] at h
    exact congrArg (fun z : ℤ => (z : ℚ)) h.symm
  have hshear (a b c t : ℤ) : F a b c = F a (b + t * c + t ^ 2 * a) (c + 2 * t * a) := by
    have h := LineBundle.ClassEulerIsomorphism.lineBundleClassEuler_pullback_overIso (Product.ShearIsomorphisms.productShearIso A.abelian.scheme t)
      (Polarization.ShearClasses.polarizationSquareClass A.dual A.polarization.isogeny.hom a b c)
    rw [Polarization.ShearClasses.polarizationSquareClass_pullback_shear A.dual A.polarization.isogeny.hom L e] at h
    exact congrArg (fun z : ℤ => (z : ℚ)) h.symm
  have hdiag (a b : ℤ) : F a b 0 = (d : ℚ) * (a : ℚ) ^ g * (b : ℚ) ^ g := by
    dsimp only [F]
    rw [Polarization.ShearClasses.polarizationSquareClass_as_bundles, zpow_zero, mul_one]
    have h := A.graphBundle_external_integerClasses_euler hN hNk a b
    exact_mod_cast h
  have hB : F 0 0 1 = (-1 : ℚ) ^ g * ((∏ i, δ i : ℕ) : ℚ) ^ 2 := by
    dsimp only [F]
    simp only [Polarization.ShearClasses.polarizationSquareClass_as_bundles, zpow_zero, zpow_one, one_mul]
    exact_mod_cast A.polarizationBiextension_euler hg hN hNk
  have h := ShearEulerIdentity.shear_euler_coefficient_identity F g (d : ℚ) hA hC hswap hshear hdiag
  rw [hB] at h
  have hsign : (-1 : ℚ) ^ g ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs : (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf : ℚ) ^ 2 =
      (2 : ℚ) ^ (2 * g) * ((∏ i, δ i : ℕ) : ℚ) ^ 2 := by
    apply mul_left_cancel₀ hsign
    calc
      _ = (2 : ℚ) ^ (2 * g) * ((-1 : ℚ) ^ g * ((∏ i, δ i : ℕ) : ℚ) ^ 2) := by
        simpa only [d, Int.cast_pow] using h.symm
      _ = _ := by ring
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_pow, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [mul_pow, ← pow_mul]
  simpa only [Nat.mul_comm] using hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
