import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.TorsorFiniteEtaleNormalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Normalized Product Map -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedProductMap.Construction

noncomputable section

/-! A finite etale product cover remains finite etale over the product with its normalization base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {S A B T : Scheme.{u}} (p : A ⟶ S) [IsProper p]
  (q : B ⟶ S) (t : T ⟶ pullback p q) [IsFinite t]

/-- The actual map from the product cover to its product with the relative normalization base. -/
def normalizedProductMap : T ⟶ pullback p ((t ≫ pullback.snd p q).fromNormalization ≫ q) :=
  pullback.lift t (t ≫ pullback.snd p q).toNormalization
    (Scheme.Hom.toNormalization_fromNormalization _).symm ≫
      (pullbackLeftPullbackSndIso p q (t ≫ pullback.snd p q).fromNormalization).hom

@[reassoc]
theorem normalizedProductMap_snd :
    normalizedProductMap p q t ≫ pullback.snd p ((t ≫ pullback.snd p q).fromNormalization ≫ q) =
      (t ≫ pullback.snd p q).toNormalization := by
  simp [normalizedProductMap, pullbackLeftPullbackSndIso_hom_snd]

@[reassoc]
theorem normalizedProductMap_fst :
    normalizedProductMap p q t ≫ pullback.fst p ((t ≫ pullback.snd p q).fromNormalization ≫ q) =
      t ≫ pullback.fst p q := by
  simp [normalizedProductMap, pullbackLeftPullbackSndIso_hom_fst]

theorem normalizedProductMap_finite
    [IsFinite (t ≫ pullback.snd p q).fromNormalization] : IsFinite (normalizedProductMap p q t) := by
  let a := pullback.lift t (t ≫ pullback.snd p q).toNormalization
    (Scheme.Hom.toNormalization_fromNormalization _).symm
  let b := pullback.fst (pullback.snd p q) (t ≫ pullback.snd p q).fromNormalization
  have : IsFinite (a ≫ b) := by simpa [a, b] using ‹IsFinite t›
  have : IsFinite a := IsFinite.of_comp a b
  change IsFinite (a ≫ _)
  infer_instance

theorem normalizedProductMap_etale [Etale t]
    [Etale (t ≫ pullback.snd p q).fromNormalization] : Etale (normalizedProductMap p q t) := by
  let a := pullback.lift t (t ≫ pullback.snd p q).toNormalization
    (Scheme.Hom.toNormalization_fromNormalization _).symm
  let b := pullback.fst (pullback.snd p q) (t ≫ pullback.snd p q).fromNormalization
  have : Etale (a ≫ b) := by simpa [a, b] using ‹Etale t›
  have : Etale a := Etale.of_comp a b
  change Etale (a ≫ _)
  infer_instance

attribute [local instance] FiniteTorsor.App.Construction.FiniteCoefficientExtension.gluedSchemeToBase_finite

/-- The actual finite-coefficient torsor is finite etale over the product with its actual normalization. -/
theorem productTorsor_normalizedProductMap_finite_etale {K : Type u} [Field K]
    {A B : Scheme.{u}} [IsIntegral B]
    (p : A ⟶ Spec (CommRingCat.of K)) [IsProper p] [Smooth p]
    (q : B ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q]
    {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n (pullback p q)) :
    IsFinite (normalizedProductMap p q E.gluedSchemeToBase) ∧
      Etale (normalizedProductMap p q E.gluedSchemeToBase) := by
  have : IsFinite E.gluedSchemeToBase := E.gluedSchemeToBase_finite
  have : Etale E.gluedSchemeToBase := E.gluedSchemeToBase_etale
  obtain ⟨hf, he⟩ := Product.TorsorFiniteEtaleNormalization.Construction.productTorsor_fromNormalization_finite_etale p q E
  have : IsFinite (E.gluedSchemeToBase ≫ pullback.snd p q).fromNormalization := hf
  have : Etale (E.gluedSchemeToBase ≫ pullback.snd p q).fromNormalization := he
  exact ⟨normalizedProductMap_finite p q E.gluedSchemeToBase,
    normalizedProductMap_etale p q E.gluedSchemeToBase⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedProductMap.Construction
