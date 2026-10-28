import OAI.ArithmeticGeometry.Models.SpreadingOut.Coefficient
import OAI.ArithmeticGeometry.Models.SpreadingOut.CoverDescent

/-! # Cover -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Cover.Construction

noncomputable section

/-! Arithmetic models obtained from proper covering models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u

theorem proper_integral_model_as_coefficient_model
    {K : Type u} [Field K] [NumberField K]
    {X : Over (Spec (.of K))}
    (P : Over (Spec (.of (𝓞 K)))) [IsProper P.hom]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))).obj P ≅ X) :
    ∃ M : Foundations.Constructions.CoefficientModel K X, IsProper M.model.hom := by
  let s : Finset K := ∅
  let A := CoefficientSystem.Constructions.Foundations.coefficientRing (𝓞 K) K s
  let f := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) A))
  let g := CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s
  let M := (Over.pullback f).obj P
  have hgf : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) A)) = _
    rw [← Spec.map_comp]
    congr 1
  have : IsProper M.hom := inferInstanceAs (IsProper (pullback.snd P.hom f))
  have := ModelFiniteness.Constructions.Foundations.coefficientBase_locallyNoetherian K s
  refine ⟨{
    coefficients := s
    model := M
    finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
    genericIso := BaseChange.Constructions.Foundations.iteratedBaseChangeIso f g P ≪≫ Scheme.Constructions.Foundations.baseChangeCongr hgf P ≪≫ e
  }, inferInstance⟩

theorem arithmetic_model_of_proper_coefficient_cover
    {K : Type u} [Field K] [NumberField K]
    {Z X : Over (Spec (.of K))} [Smooth X.hom] [IsProper X.hom]
    (f : Z ⟶ X) [Surjective f.left]
    (P : Foundations.Constructions.CoefficientModel K Z) [IsProper P.model.hom] :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : Over B.U.toScheme),
      Smooth M.hom ∧ IsProper M.hom ∧
      Nonempty ((Over.pullback B.generic).obj M ≅ X) := by
  obtain ⟨M, hM⟩ := CoverDescent.Construction.proper_model_of_cover
    (show Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom from ⟨inferInstance, inferInstance, inferInstance⟩)
    f P
  have := hM
  exact Coefficient.Construction.proper_coefficient_model_to_arithmetic M

theorem arithmetic_model_of_proper_integral_cover
    {K : Type u} [Field K] [NumberField K]
    {Z X : Over (Spec (.of K))} [Smooth X.hom] [IsProper X.hom]
    (f : Z ⟶ X) [Surjective f.left]
    (P : Over (Spec (.of (𝓞 K)))) [IsProper P.hom]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) K)))).obj P ≅ Z) :
    ∃ (B : Base.Construction.ArithmeticOpen K) (M : Over B.U.toScheme),
      Smooth M.hom ∧ IsProper M.hom ∧
      Nonempty ((Over.pullback B.generic).obj M ≅ X) := by
  obtain ⟨P₀, hP₀⟩ := proper_integral_model_as_coefficient_model P e
  have := hP₀
  exact arithmetic_model_of_proper_coefficient_cover f P₀

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Cover.Construction
