import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationQuotient

/-! # Relation Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationLift

noncomputable section

/-!
# IntegralComparison: universal factorization through a crystalline relation quotient
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationQuotient

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {U W : BigCrystallineSite.Object p B J δ f} (S : Set U.ring) (hS : S ⊆ U.ideal)
variable (β : W ⟶ U) (hβ : ∀ x ∈ S, β.ringMap x = 0)

def liftDP : DividedPowers.DPMorphism (RelationQuotient.dividedPowers U S hS) W.dividedPowers :=
  DividedPower.Relations.lift U.dividedPowers S hS β.ringMap hβ

lemma liftDP_comp : (liftDP S hS β hβ).comp (RelationQuotient.quotientDP U S hS) = β.ringMap :=
  DividedPower.Relations.lift_comp U.dividedPowers S hS β.ringMap hβ

private lemma quotient_comp :
    (BigCrystallineSite.Object.quotientMap W (RelationQuotient.object U S hS) (liftDP S hS β hβ)).comp
      (BigCrystallineSite.Object.quotientMap (RelationQuotient.object U S hS) U (RelationQuotient.quotientDP U S hS)) = BigCrystallineSite.Object.quotientMap W U β.ringMap := by
  rw [← BigCrystallineSite.Object.quotientMap_comp, liftDP_comp]

def liftHom : W ⟶ RelationQuotient.object U S hS where
  ringMap := liftDP S hS β hβ
  overBase := by
    change (liftDP S hS β hβ).toRingHom.comp ((RelationQuotient.quotientRingMap U S).comp U.base) = W.base
    change β.ringMap.toRingHom.comp U.base = W.base
    exact β.overBase
  overX := by
    change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap W (RelationQuotient.object U S hS) (liftDP S hS β hβ))) ≫
      (RelationQuotient.closedMap U S ≫ U.mapToX) = W.mapToX
    rw [← Category.assoc]
    have hq : Spec.map (CommRingCat.ofHom
          (BigCrystallineSite.Object.quotientMap W (RelationQuotient.object U S hS) (liftDP S hS β hβ))) ≫ RelationQuotient.closedMap U S =
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap W U β.ringMap)) := by
      change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap W (RelationQuotient.object U S hS) (liftDP S hS β hβ))) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap (RelationQuotient.object U S hS) U (RelationQuotient.quotientDP U S hS))) = _
      rw [← Spec.map_comp]
      exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) (quotient_comp S hS β hβ)
    rw [hq]
    exact β.overX

lemma liftHom_comp : liftHom S hS β hβ ≫ RelationQuotient.hom U S hS = β := by
  apply BigCrystallineSite.Object.Hom.ext
  exact liftDP_comp S hS β hβ

lemma liftHom_unique (γ : W ⟶ RelationQuotient.object U S hS) (hγ : γ ≫ RelationQuotient.hom U S hS = β) : γ = liftHom S hS β hβ := by
  apply BigCrystallineSite.Object.Hom.ext
  apply DFunLike.ext
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact congrArg (fun t : W ⟶ U => t.ringMap x) hγ

include hβ in
lemma existsUnique_factorization : ∃! γ : W ⟶ RelationQuotient.object U S hS, γ ≫ RelationQuotient.hom U S hS = β :=
  ⟨liftHom S hS β hβ, liftHom_comp S hS β hβ, fun γ hγ => liftHom_unique S hS β hβ γ hγ⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelationLift
