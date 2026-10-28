import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticDiagrams

/-! # Arithmetic Point Spreading -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticPointSpreading

noncomputable section

/-! A specified rational point extends to a section of the original
model after enlarging the denominator. Its generic value is preserved. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem point_on_fixed_arithmetic_model_spreads
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) (X : Over B.base)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom)
    (x : Spec (.of B.extension.carrier) ⟶ X.left) (hx : x ≫ X.hom = B.generic) :
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D),
      ∃ z : (B.withDenominator D hD).base ⟶ X.left,
        z ≫ X.hom = ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv ∧
        (B.withDenominator D hD).generic ≫ z = x := by
  let S : Over B.base := Over.mk (𝟙 B.base)
  let G : Over (Spec (.of B.extension.carrier)) := Over.mk (𝟙 _)
  let H := (Over.pullback B.generic).obj X
  let a : G ⟶ H := Over.homMk (pullback.lift x (𝟙 _) (by
    simpa only [Category.id_comp] using hx)) (pullback.lift_snd _ _ _)
  have hS : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism S.hom := by
    change ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (𝟙 B.base)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hG : IsPullback B.generic G.hom S.hom B.generic := IsPullback.of_id_snd
  have hH : IsPullback (pullback.fst X.hom B.generic) H.hom X.hom B.generic :=
    IsPullback.of_hasPullback X.hom B.generic
  obtain ⟨D, hD, hdiv, b, hb⟩ := FixedArithmeticDiagrams.morphism_between_fixed_arithmetic_models_spreads B S X hS hX
    B.generic (pullback.fst X.hom B.generic) hG hH a
  let B' := B.withDenominator D hD
  let u := ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv
  let σ : B'.base ⟶ ((Over.pullback u).obj S).left :=
    pullback.lift u (𝟙 _) (by
      change u ≫ 𝟙 B.base = 𝟙 B'.base ≫ u
      rw [Category.comp_id, Category.id_comp])
  have hσ : B'.generic ≫ σ = FixedArithmeticDiagrams.arithmeticModelProjection B S (G := G) B.generic hG.w D hD hdiv := by
    apply pullback.hom_ext
    · change (B'.generic ≫ σ) ≫ pullback.fst S.hom u = _
      rw [Category.assoc, pullback.lift_fst, FixedArithmeticDiagrams.arithmeticModelProjection_fst]
      exact ArithmeticBaseMaps.arithmeticEnlargement_generic B D hD hdiv
    · change (B'.generic ≫ σ) ≫ pullback.snd S.hom u = _
      rw [Category.assoc, pullback.lift_snd, Category.comp_id, FixedArithmeticDiagrams.arithmeticModelProjection_snd]
      exact (Category.id_comp _).symm
  refine ⟨D, hD, hdiv, σ ≫ b.left ≫ pullback.fst X.hom u, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc b.left]
    change σ ≫ (b.left ≫ ((Over.pullback u).obj X).hom) ≫ u = _
    rw [b.w, ← Category.assoc]
    exact (congrArg (fun f => f ≫ u) (pullback.lift_snd u (𝟙 B'.base) _)).trans
      (Category.id_comp _)
  · rw [← Category.assoc, hσ, ← Category.assoc, hb, Category.assoc,
      FixedArithmeticDiagrams.arithmeticModelProjection_fst]
    exact pullback.lift_fst _ _ _

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticPointSpreading
