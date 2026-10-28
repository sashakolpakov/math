import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseTower
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedDiagramTransport

/-! # Effective Albanese Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.EffectiveAlbaneseDescent

noncomputable section

/-! Effective number-field descent of the specified pointed complex
Albanese. Both the abelian scheme and the original map are constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]

theorem effective_arithmetic_albanese_descent
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver)
    (ha : Albanese.IsAlbaneseMap (AlbaneseArithmeticIsogeny.complexSourcePresentation X P)
      (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀) A a)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
      (Y : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of B.extension.carrier)))
      (r : (Over.pullback B.fieldExtension).obj X ⟶ Y.toOver)
      (eX : (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj
          ((Over.pullback B.fieldExtension).obj X) ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X)
      (eY : (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).obj Y.toOver ≅ A.toOver),
      B.denominator = N ∧ IsMonHom eY.hom ∧
        Section.Comparisons.mappedSection (Over.pullback B.fieldExtension) x₀ ≫ r = 1 ∧
        Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding)))
          (Section.Comparisons.mappedSection (Over.pullback B.fieldExtension) x₀) ≫ eX.hom =
            Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀ ∧
        (Over.pullback (Spec.map (CommRingCat.ofHom B.embedding))).map r ≫ eY.hom =
          eX.hom ≫ a := by
  obtain ⟨B, n, T, φ, _, _, hφMon, hφ, hφFinite, hφEtale, hφSurj⟩ :=
    AlbaneseArithmeticIsogeny.albanese_arithmetic_isogeny_target X x₀ P A a ha N hN
  let := hφMon
  let := hφFinite
  let := hφEtale
  let := hφSurj
  obtain ⟨C, Y, r, eY, hC, heY, hrPoint, hr⟩ :=
    Arithmetic.AlbaneseTower.arithmetic_albanese_map_descends_over_tower X x₀ A a ha.1 T φ hφ N hN
  let D := B.compose C
  let P₁ := Over.pullback B.fieldExtension
  let P₂ := Over.pullback C.fieldExtension
  let u : Spec (.of C.extension.carrier) ⟶ Spec (.of R) := D.fieldExtension
  let P₃ : Over (Spec (.of R)) ⥤ Over (Spec (.of C.extension.carrier)) := Over.pullback u
  let F := Over.pullback (Spec.map (CommRingCat.ofHom C.embedding))
  let H := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))
  let k : P₂.obj (P₁.obj X) ≅ P₃.obj X := (B.composeSourceNatIso C).app X
  let e := Arithmetic.TowerComparison.arithmeticTowerComplexSourceIso B C X
  have hk : Section.Comparisons.mappedSection P₂ (Section.Comparisons.mappedSection P₁ x₀) ≫ k.hom = Section.Comparisons.mappedSection P₃ x₀ :=
    Section.Comparisons.mappedSection_comp_naturality P₁ P₂ P₃ (B.composeSourceNatIso C).hom x₀
  have hp : Section.Comparisons.mappedSection P₃ x₀ ≫ (k.inv ≫ r) = 1 :=
    PointedDiagramTransport.pointed_map_change_source k _ _ r hk hrPoint
  have hs : Section.Comparisons.mappedSection F (Section.Comparisons.mappedSection P₃ x₀) ≫ (F.mapIso k.symm ≪≫ e).hom =
      Section.Comparisons.mappedSection H x₀ := PointedDiagramTransport.mapped_section_change_source F k _ _ e _ hk
        (Arithmetic.TowerComparison.arithmeticTowerComplexSourceIso_point B C x₀)
  have hm : F.map (k.inv ≫ r) ≫ eY.hom = (F.mapIso k.symm ≪≫ e).hom ≫ a :=
    PointedDiagramTransport.baseChanged_map_change_source F k r a e eY hr
  exact ⟨D, Y, k.inv ≫ r, F.mapIso k.symm ≪≫ e, eY, hC, heY, hp, hs, hm⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.EffectiveAlbaneseDescent
