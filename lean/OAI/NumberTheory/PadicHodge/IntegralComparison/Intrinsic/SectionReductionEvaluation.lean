import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionEvaluation

/-! # Section Reduction Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionReductionEvaluation

noncomputable section

/-! Evaluation along actual geometric sections commutes with a
specified change of base and its commuting section square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem appLE_congr {P Q : Scheme} (f g : P ⟶ Q) (h : f = g)
    (U : Q.Opens) (V : P.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

universe u
variable {R S : Type u} [CommRing R] [CommRing S] (ρ : R →+* S)
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (sX : Spec (CommRingCat.of R) ⟶ X.left) (hsX : sX ≫ X.hom = 𝟙 _)
  (sY : Spec (CommRingCat.of S) ⟶ Y.left) (hsY : sY ≫ Y.hom = 𝟙 _)
  (h : sY ≫ f = Spec.map (CommRingCat.ofHom ρ) ≫ sX)
  (U : X.left.Opens) (hU : ⊤ ≤ sX ⁻¹ᵁ U) (hV : ⊤ ≤ sY ⁻¹ᵁ (f ⁻¹ᵁ U))

include h in
theorem evaluation (a : Γ(X.left, U)) :
    SectionEvaluation.evaluation S Y sY hsY (f ⁻¹ᵁ U) hV (f.app U a) =
      ρ (SectionEvaluation.evaluation R X sX hsX U hU a) := by
  have happ : f.app U ≫ sY.appLE (f ⁻¹ᵁ U) ⊤ hV =
      sX.appLE U ⊤ hU ≫ (Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ le_top := by
    rw [← Scheme.Hom.comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr _ _ h U ⊤ _ _
  have htop : (Spec.map (CommRingCat.ofHom ρ)).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom ρ)).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  have hs : (f.app U ≫ sY.appLE (f ⁻¹ᵁ U) ⊤ hV) ≫
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
      (sX.appLE U ⊤ hU ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫
        CommRingCat.ofHom ρ := by
    rw [happ, Category.assoc, htop, Scheme.ΓSpecIso_naturality, Category.assoc]
  exact ConcreteCategory.congr_hom hs a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.SectionReductionEvaluation
