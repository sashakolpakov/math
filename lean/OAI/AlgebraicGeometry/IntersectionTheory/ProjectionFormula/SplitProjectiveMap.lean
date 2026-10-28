import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousLocalizationAutomorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Dimension

/-! # Split Projective Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitProjectiveMap

noncomputable section

/-! A split graded coordinate quotient induces an actual closed
embedding of projective spaces. Both topology and stalk surjectivity
are proved for the native Proj morphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading n →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading m)
  (g : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (hfg : ∀ r, f (g r) = r)

include hfg

theorem irrelevant_le : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) ≤
    (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).map f := by
  apply Projective.LinearChart.Automorphism.irrelevant_le_of_inverse f g
  ext r : 1
  exact hfg r

def map : Foundations.Scheme.ProjectiveSpace.projectiveSpace m ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := Proj.map f (irrelevant_le f g hfg)

theorem injective : Function.Injective (SplitProjectiveMap.map f g hfg) := by
  intro p q he
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext
  apply Ideal.comap_injective_of_surjective f.toRingHom (fun r => ⟨g r, hfg r⟩)
  exact congrArg (fun x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n => x.asHomogeneousIdeal.toIdeal) he

theorem local_surjective (p : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) :
    Function.Surjective (HomogeneousLocalization.localRingHom f
      (p.asHomogeneousIdeal.toIdeal.comap f.toRingHom) p.asHomogeneousIdeal.toIdeal rfl) := by
  let P := p.asHomogeneousIdeal.toIdeal
  let Q := P.comap f.toRingHom
  have hg : P.primeCompl ≤ Q.primeCompl.comap g := by
    intro a ha
    change f (g a) ∉ P
    rw [hfg]
    exact ha
  have hf : Q.primeCompl ≤ P.primeCompl.comap f := le_rfl
  intro b
  refine ⟨HomogeneousLocalization.map g hg b, ?_⟩
  exact HomogeneousLocalizationAutomorphism.map_inverse g f hg hf hfg b

theorem stalk_surjective (p : Foundations.Scheme.ProjectiveSpace.projectiveSpace m) : Function.Surjective ((SplitProjectiveMap.map f g hfg).stalkMap p) := by
  change Function.Surjective ((Proj.sheafedSpaceMap f (irrelevant_le f g hfg)).hom.stalkMap p)
  rw [← Proj.localRingHom_comp_stalkIso]
  exact (ConcreteCategory.bijective_of_isIso (Proj.stalkIso (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) p).inv).surjective.comp
    ((local_surjective f g hfg p).comp
      (ConcreteCategory.bijective_of_isIso
        (Proj.stalkIso (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (ProjectiveSpectrum.comap f (irrelevant_le f g hfg) p)).hom).surjective)

theorem over_base (hC : ∀ c : ℂ, f (MvPolynomial.C c) = MvPolynomial.C c) :
    SplitProjectiveMap.map f g hfg ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n = Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m :=
  Projective.LinearChart.OverBase.graded_over_base f (irrelevant_le f g hfg) hC

theorem closed (hC : ∀ c : ℂ, f (MvPolynomial.C c) = MvPolynomial.C c) : IsClosedImmersion (SplitProjectiveMap.map f g hfg) := by
  have hc : IsProper (SplitProjectiveMap.map f g hfg ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := by
    rw [over_base f g hfg hC]
    infer_instance
  let := hc
  let : IsProper (SplitProjectiveMap.map f g hfg) := IsProper.of_comp (SplitProjectiveMap.map f g hfg) (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let : SurjectiveOnStalks (SplitProjectiveMap.map f g hfg) := ⟨stalk_surjective f g hfg⟩
  exact ⟨.of_continuous_injective_isClosedMap (SplitProjectiveMap.map f g hfg).continuous
    (injective f g hfg) (SplitProjectiveMap.map f g hfg).isClosedMap⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SplitProjectiveMap
