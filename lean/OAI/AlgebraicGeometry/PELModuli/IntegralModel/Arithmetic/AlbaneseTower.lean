import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseArithmeticIsogeny
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.IsogenyDiagram
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicPointedSections
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.TowerComparison

/-! # Albanese Tower -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseTower

noncomputable section

/-! Descend the specified pointed map along the constructed arithmetic
isogeny, using uniqueness of unramified pointed lifts on fpqc overlaps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]

theorem arithmetic_albanese_map_descends_over_tower
    {B : Base.ArithmeticBaseExtension R (algebraMap R ℂ)}
    (X : Over (Spec (.of R))) [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver)
    (ha : Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀ ≫ a = 1)
    {n m : ℕ} (T : GeneratingTarget.ArithmeticGeneratingTarget B X x₀ A.toOver n m)
    (φ : A.toOver ⟶ T.complexTarget) [IsMonHom φ]
    [IsFinite φ.left] [Etale φ.left] [Surjective φ.left]
    (hφ : a ≫ φ = T.complexMap) (N : ℕ) (hN : N ≠ 0) :
    ∃ (C : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
      (Y : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of C.extension.carrier)))
      (r : (Over.pullback C.fieldExtension).obj ((Over.pullback B.fieldExtension).obj X) ⟶ Y.toOver)
      (eY : (Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))).obj Y.toOver ≅ A.toOver),
      C.denominator = N ∧ IsMonHom eY.hom ∧
        Section.Comparisons.mappedSection (Over.pullback C.fieldExtension)
          (Section.Comparisons.mappedSection (Over.pullback B.fieldExtension) x₀) ≫ r = 1 ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))).map r ≫ eY.hom =
          (TowerComparison.arithmeticTowerComplexSourceIso B C X).hom ≫ a := by
  have : Smooth A.toOver.hom := A.variety.presentation.smooth
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsIntegral A.toOver.left := A.variety.property
  have : GeometricallyConnected A.toOver.hom :=
    ArithmeticGeometry.Models.SpreadingOut.GeometricFieldComponents.Construction.integral_geometricallyConnected_over_algClosed A.toOver.hom
  let φ₀ : A.toOver ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj T.target.toOver := φ
  have : IsMonHom φ₀ := inferInstanceAs (IsMonHom φ)
  have : IsFinite φ₀.left := inferInstanceAs (IsFinite φ.left)
  have : Etale φ₀.left := inferInstanceAs (Etale φ.left)
  have : Surjective φ₀.left := inferInstanceAs (Surjective φ.left)
  have hφ₀ : a ≫ φ₀ = T.complexMap := hφ
  obtain ⟨C, Y, q, eY, hC, heY, hqGroup, hqFinite, hqEtale, _, hq⟩ :=
    IsogenyDiagram.finite_etale_isogeny_diagram_descends B.embedding T.target.toOver A.toOver φ₀ N hN
  let := heY
  let := hqGroup
  let := hqFinite
  let := hqEtale
  let P := Over.pullback B.fieldExtension
  let Q := Over.pullback C.fieldExtension
  let γ := Spec.map (CommRingCat.ofHom C.embedding)
  let F := Over.pullback γ
  let G := Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let c := ComplexComparison.GroupBaseChange.arithmeticComplexNatIso C
  let d := ComplexComparison.GroupBaseChange.arithmeticComplexNatIso B
  let eX := TowerComparison.arithmeticTowerComplexSourceIso B C X
  let f : A.toOver ⟶ F.obj (Q.obj T.target.toOver) := φ₀ ≫ (c.app T.target.toOver).inv
  have hq' : F.map q = eY.hom ≫ f := by
    have hc : F.map q ≫ (c.app T.target.toOver).hom = eY.hom ≫ φ₀ := by
      change F.map q ≫ ((ComplexComparison.GroupBaseChange.arithmeticComplexNatIso C).app T.target.toOver).hom = _
      rw [ComplexComparison.GroupBaseChange.arithmeticComplexNatIso_hom_app]
      exact hq
    rw [← cancel_mono (c.app T.target.toOver).hom]
    simpa only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  have hb₀ : eX.hom ≫ a ≫ φ₀ = F.map (Q.map T.map) ≫ (c.app T.target.toOver).hom := by
    have hn : F.map (Q.map T.map) ≫ (c.app T.target.toOver).hom =
        (c.app (P.obj X)).hom ≫ G.map T.map := c.hom.naturality T.map
    dsimp only [eX, TowerComparison.arithmeticTowerComplexSourceIso, Iso.trans_hom]
    simp only [Category.assoc]
    change (c.app (P.obj X)).hom ≫ (d.app X).hom ≫ a ≫ φ₀ = _
    rw [hφ₀]
    change (c.app (P.obj X)).hom ≫ (d.app X).hom ≫ (d.app X).inv ≫ G.map T.map = _
    rw [Iso.hom_inv_id_assoc]
    exact hn.symm
  have hb : eX.hom ≫ a ≫ f = F.map (Q.map T.map) := by
    rw [← cancel_mono (c.app T.target.toOver).hom]
    simpa only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hb₀
  have : GeometricallyConnected (P.obj X).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd X.hom B.fieldExtension))
  have : GeometricallyConnected (Q.obj (P.obj X)).hom := inferInstanceAs
    (GeometricallyConnected (pullback.snd (P.obj X).hom C.fieldExtension))
  have : Flat γ := inferInstance
  have : QuasiCompact γ := inferInstance
  have : Surjective γ := ⟨Function.surjective_to_subsingleton _⟩
  obtain ⟨r, _, hrPoint, hr⟩ := IntrinsicPointedSections.pointed_map_descends_through_unramified_comparison
    γ (Q.obj (P.obj X)) Y.toOver (Q.obj T.target.toOver) q (Q.map T.map)
    (Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection P x₀)) (H.obj X) A.toOver (Section.Comparisons.mappedSection H x₀)
    eX eY a f ha (TowerComparison.arithmeticTowerComplexSourceIso_point B C x₀) hq' hb
  exact ⟨C, Y, r, eY, hC, heY, hrPoint, hr⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseTower
