import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RepresentativePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacterNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectivePresentationMorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCharacter

/-! # Pullback Character -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PullbackCharacter

noncomputable section

/-! The actual finite H¹ overlap character commutes with inverse image
along any scheme morphism and a compatible map between the covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (U D : Y.ProEt) (a b : D ⟶ U) (V E : X.ProEt) (c d : E ⟶ V)
  [PreconnectedSpace U.left] [PreconnectedSpace V.left]
  (hzero : ∀ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).H 1, AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n U.hom 1 x = 0)
  (kzero : ∀ x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).H 1, AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n V.hom 1 x = 0)
  (rU : V ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj U) (rD : E ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj D)
  (ha : rD ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map a = c ≫ rU)
  (hb : rD ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map b = d ≫ rU)

include ha hb in
theorem character_pullback (x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).H 1) :
    CoverCharacter.character ℓ n V E c d kzero (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x) =
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f).hom.app (op E)
        (ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) rD
          (CoverCharacter.character ℓ n U D a b hzero x)) := by
  let S := CoverCharacter.presentation ℓ n Y
  let R := CoverCharacter.presentation ℓ n X
  let hS := CoverCharacter.presentation_shortExact ℓ n (X := Y)
  let hR := CoverCharacter.presentation_shortExact ℓ n (X := X)
  let hSlift := CoverFiniteness.presentation_local_lifts ℓ n
    S.X₂ S.X₃ S.f S.g S.zero hS U hzero
  let hRlift := CoverFiniteness.presentation_local_lifts ℓ n
    R.X₂ R.X₃ R.f R.g R.zero hR V kzero
  let rS := CoverCharacter.representative S hS U D a b hSlift x
  let T := PresentationPullback.complex ℓ n f S.X₂ S.X₃ S.f S.g S.zero
  let hT := PresentationPullback.shortExact ℓ n f S.X₂ S.X₃ S.f S.g S.zero hS
  let rT := RepresentativePullback.representative ℓ n f S.X₂ S.X₃ S.f S.g S.zero hS
    U D a b V E c d rU rD ha hb rS
  obtain ⟨φ, hφ⟩ := InjectivePresentationMorphism.exists_morphism hT (T := R)
    (𝟙 (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X))
  let r₀ := CoverCharacterNaturality.mapRepresentative hT hR φ V E V E c d c d
    (𝟙 V) (𝟙 E) (by simp) (by simp) rT
  have hc : Sheaf.H.map φ.τ₁ 1 (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x) =
      AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x := by
    rw [hφ]
    exact Sheaf.H.map_id_apply _
  let r : CoverCharacter.Representative R hR V E c d (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x) := {
    z := r₀.z, t := r₀.t, c := r₀.c
    class_eq := r₀.class_eq.trans hc, lift_eq := r₀.lift_eq, difference_eq := r₀.difference_eq }
  have he := CoverCharacter.representative_unique R hR V E c d
    (CoverCharacter.coefficient_restrictions_eq ℓ n c d)
    (CoverCharacter.representative R hR V E c d hRlift (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x)) r
  change CoverCharacter.character ℓ n V E c d kzero (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x) =
    φ.τ₁.hom.app (op E) (T.X₁.obj.map (𝟙 E).op
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f).hom.app (op E)
        (ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) rD
          (CoverCharacter.character ℓ n U D a b hzero x)))) at he
  rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, hφ] at he
  exact he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PullbackCharacter
