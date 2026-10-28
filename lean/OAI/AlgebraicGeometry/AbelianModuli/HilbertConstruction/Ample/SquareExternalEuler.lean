import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompactExternalAcyclicEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ExternalSquareEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SerreVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Square External Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SquareExternalEuler

noncomputable section

/-! External Euler characteristics multiply for arbitrary line bundles
on the square of a projective abelian variety. Ample twists prove the
formula on an eventual grid; integer Euler polynomials remove the twists. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u

theorem lineBundleClass_pullback_tensorPower
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M H : Line.Bundles.LineBundle Y) (n : ℕ) :
    Line.Bundles.LineBundle.classOf ((M.tensor (H.tensorPower n)).pullback f) =
      Line.Bundles.LineBundle.classOf (M.pullback f) * Line.Bundles.LineBundle.classOf (H.pullback f) ^ n := by
  let e : ((M.tensor (H.tensorPower n)).pullback f).sheaf ≅
      ((M.pullback f).tensor ((H.pullback f).tensorPower n)).sheaf :=
    Line.Bundles.LineBundle.tensorBaseChangeIso f M (H.tensorPower n) ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (H.powerBaseChangeIso f n)
  calc
    _ = Line.Bundles.LineBundle.classOf ((M.pullback f).tensor ((H.pullback f).tensorPower n)) :=
      Quotient.sound ⟨e⟩
    _ = _ := by rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_tensorPower]

theorem abelianSquare_external_euler
    {k : Type u} [Field k] {g : ℕ} (A : Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (H : Line.Bundles.LineBundle A.scheme.left) (hH : H.IsAmple)
    (M N : Line.Bundles.LineBundle A.scheme.left) :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (A.scheme ⊗ A.scheme).hom
        (Line.Bundles.LineBundle.externalTensor A.scheme.hom A.scheme.hom M N).sheaf =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom M.sheaf *
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom N.sheaf := by
  let p := (A.scheme ⊗ A.scheme).hom
  let f := (fst A.scheme A.scheme).left
  let h := (snd A.scheme A.scheme).left
  let H₁ := H.pullback f
  let H₂ := H.pullback h
  let M₁ := M.pullback f
  let N₂ := N.pullback h
  let q := Line.Bundles.LineBundle.classOf M₁ * Line.Bundles.LineBundle.classOf N₂
  have : IsProper p := inferInstanceAs
    (IsProper (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom))
  have : Flat p := inferInstanceAs
    (Flat (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom))
  have : LocallyOfFinitePresentation p := inferInstanceAs
    (LocallyOfFinitePresentation (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom))
  have : A.scheme.left.IsSeparated := by
    constructor
    rw [← terminal.comp_from A.scheme.hom]
    infer_instance
  have : (Limits.pullback (C := Scheme.{u}) A.scheme.hom A.scheme.hom).IsSeparated := by
    constructor
    rw [← terminal.comp_from (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom)]
    infer_instance
  have : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  let E := (hH.exists_powerProjectiveEmbedding A.scheme.hom).some
  let E₂ := ExternalSquareEmbedding.ampleExternalSquarePowerEmbedding (A := A.scheme) H hH
  let F : ℤ → ℤ → ℚ := fun a b =>
    (LineBundle.EulerShifts.lineBundleClassEuler p
      (q * Line.Bundles.LineBundle.classOf H₁ ^ a * Line.Bundles.LineBundle.classOf H₂ ^ b) : ℚ)
  let G : ℤ → ℤ → ℚ := fun a b =>
    (LineBundle.EulerShifts.lineBundleClassEuler A.scheme.hom (Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf H ^ a) : ℚ) *
      (LineBundle.EulerShifts.lineBundleClassEuler A.scheme.hom (Line.Bundles.LineBundle.classOf N * Line.Bundles.LineBundle.classOf H ^ b) : ℚ)
  have hF₁ (b : ℤ) : ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b := by
    obtain ⟨P, hP⟩ := E₂.lineBundleClass_integerEulerPolynomial p H₁
      (q * Line.Bundles.LineBundle.classOf H₂ ^ b)
    exact ⟨P, fun a => by simpa only [F, mul_assoc, mul_left_comm, mul_comm] using hP a⟩
  have hF₂ (a : ℤ) : ∃ P : Polynomial ℚ, ∀ b : ℤ, P.eval (b : ℚ) = F a b :=
    E₂.lineBundleClass_integerEulerPolynomial p H₂ (q * Line.Bundles.LineBundle.classOf H₁ ^ a)
  have hG₁ (b : ℤ) : ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = G a b := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial A.scheme.hom H (Line.Bundles.LineBundle.classOf M)
    refine ⟨P * Polynomial.C
      (LineBundle.EulerShifts.lineBundleClassEuler A.scheme.hom (Line.Bundles.LineBundle.classOf N * Line.Bundles.LineBundle.classOf H ^ b) : ℚ), ?_⟩
    intro a
    simp only [Polynomial.eval_mul, Polynomial.eval_C, hP, G]
  have hG₂ (a : ℤ) : ∃ P : Polynomial ℚ, ∀ b : ℤ, P.eval (b : ℚ) = G a b := by
    obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial A.scheme.hom H (Line.Bundles.LineBundle.classOf N)
    refine ⟨Polynomial.C
      (LineBundle.EulerShifts.lineBundleClassEuler A.scheme.hom (Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf H ^ a) : ℚ) * P, ?_⟩
    intro b
    simp only [Polynomial.eval_mul, Polynomial.eval_C, hP, G]
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : M.sheaf.IsFiniteType := M.isFiniteType
  have : N.sheaf.IsQuasicoherent := N.isQuasicoherent
  have : N.sheaf.IsFiniteType := N.isFiniteType
  obtain ⟨B, hB⟩ := SerreVanishing.ample_tensorPowers_eventually_vanish A.scheme.hom H hH M.sheaf
  obtain ⟨C, hC⟩ := SerreVanishing.ample_tensorPowers_eventually_vanish A.scheme.hom H hH N.sheaf
  have hgrid (a b : ℕ) (ha : B ≤ a) (hb : C ≤ b) : F a b = G a b := by
    let M' := M.tensor (H.tensorPower a)
    let N' := N.tensor (H.tensorPower b)
    let T := Line.Bundles.LineBundle.externalTensor A.scheme.hom A.scheme.hom M' N'
    have hc : Line.Bundles.LineBundle.classOf T =
        q * Line.Bundles.LineBundle.classOf H₁ ^ a * Line.Bundles.LineBundle.classOf H₂ ^ b := by
      change Line.Bundles.LineBundle.classOf ((M'.pullback f).tensor (N'.pullback h)) = _
      rw [Line.Bundles.LineBundle.classOf_tensor]
      dsimp only [M', N']
      rw [lineBundleClass_pullback_tensorPower, lineBundleClass_pullback_tensorPower]
      dsimp only [q, M₁, N₂, H₁, H₂]
      ac_rfl
    have hleft : F a b = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p T.sheaf : ℚ) := by
      dsimp only [F]
      rw [zpow_natCast, zpow_natCast, ← hc, LineBundle.EulerShifts.lineBundleClassEuler_classOf]
    have hright : G a b =
        (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom M'.sheaf : ℚ) *
          (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom N'.sheaf : ℚ) := by
      simp only [G, zpow_natCast, ← Line.Bundles.LineBundle.classOf_tensorPower,
        ← Line.Bundles.LineBundle.classOf_tensor, LineBundle.EulerShifts.lineBundleClassEuler_classOf, M', N']
    have hprod := CompactExternalAcyclicEuler.fieldExternal_euler_of_positive_vanishing_of_compact
      (IsPullback.of_hasPullback A.scheme.hom A.scheme.hom) M' N'
      (fun r => ModuleCat.subsingleton_of_isZero (hB a ha r))
      (fun r => ModuleCat.subsingleton_of_isZero (hC b hb r))
    have he : CohomologyEulerCharacteristic.coefficientEulerCharacteristic p T.sheaf =
        CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom M'.sheaf *
          CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.scheme.hom N'.sheaf := by
      change CohomologyEulerCharacteristic.coefficientEulerCharacteristic
        (pullback.fst A.scheme.hom A.scheme.hom ≫ A.scheme.hom) T.sheaf = _
      rw [pullback.condition]
      exact hprod
    rw [hleft, hright]
    exact_mod_cast he
  have hfinal := HilbertConstruction.Polynomial.EventualGrid.separately_polynomial_eq_of_eventual_grid F G hF₁ hF₂ hG₁ hG₂ B C hgrid 0 0
  apply Int.cast_injective (α := ℚ)
  change (CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((M.pullback f).tensor (N.pullback h)).sheaf : ℚ) = _
  simpa only [F, G, zpow_zero, mul_one, q, M₁, N₂, f, h,
    ← Line.Bundles.LineBundle.classOf_tensor, LineBundle.EulerShifts.lineBundleClassEuler_classOf, Int.cast_mul] using hfinal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.SquareExternalEuler
