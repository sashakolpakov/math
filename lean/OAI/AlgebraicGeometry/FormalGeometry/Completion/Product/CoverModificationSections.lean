import OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverFactorChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonDescent
import OAI.AlgebraicGeometry.FormalGeometry.Completion.StructureSheafBaseChange

/-! # Cover Modification Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverModificationSections.Construction

noncomputable section

/-! Factor modifications preserve the actual infinitesimal sections of finite etale product covers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K R : Type u} [Field K] [CommRing R] {A T D : Scheme.{u}}
  (p : A ⟶ Spec (CommRingCat.of K)) (q : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K))
  (t : T ⟶ pullback p q) [Etale t]

/-- The first-factor map stays flat on every actual infinitesimal neighborhood. -/
theorem productCover_infinitesimalFirstMap_flat (I : Ideal R) (n : ℕ) :
    Flat (pullback.fst (t ≫ pullback.snd p q) (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫
      t ≫ pullback.fst p q) := by
  have : Etale (CoverBaseChange.Construction.productCoverBaseChangeMap p q t (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)) :=
    CoverBaseChange.Construction.productCoverBaseChangeMap_etale p q t (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n)
  rw [← CoverBaseChange.Construction.productCoverBaseChangeMap_fst]
  infer_instance

/-- The modified family is flat over the literal coefficient base, even if the factor
modification itself is not flat. -/
theorem productCover_factorModification_flat (c : D ⟶ A) :
    Flat (pullback.snd c (t ≫ pullback.fst p q) ≫ (t ≫ pullback.snd p q)) := by
  have : Etale (CoverFactorChange.Construction.productCoverFactorChangeMap p q t c) := CoverFactorChange.Construction.productCoverFactorChangeMap_etale p q t c
  rw [← CoverFactorChange.Construction.productCoverFactorChangeMap_snd]
  infer_instance

variable (c : D ⟶ A) [IsProper c]
  (hc : ∀ U : A.Opens, IsAffineOpen U → IsIso (c.app U))

include hc in
/-- Global sections of the actual modified cover agree with the original cover. -/
theorem productCover_factorModification_appTop_isIso :
    IsIso (pullback.snd c (t ≫ pullback.fst p q)).appTop :=
  StructureSheafBaseChange.Construction.proper_flat_pullback_app_isIso c (t ≫ pullback.fst p q) hc ⊤

include hc in
/-- At every infinitesimal level, the literal modification pullback map is an isomorphism on
actual global sections. -/
theorem productCover_factorModification_infinitesimal_appTop_isIso (I : Ideal R) (n : ℕ) :
    IsIso (ComparisonDescent.Construction.infinitesimalNeighborhoodMap I (t ≫ pullback.snd p q)
      (pullback.snd c (t ≫ pullback.fst p q)) n).appTop := by
  let f := t ≫ pullback.snd p q
  let a := t ≫ pullback.fst p q
  let g := pullback.snd c a
  let a' := pullback.fst f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n) ≫ a
  have : Flat a' := productCover_infinitesimalFirstMap_flat p q t I n
  have H := (ComparisonDescent.Construction.infinitesimalNeighborhoodMap_isPullback I f g n).paste_vert
    (IsPullback.of_hasPullback c a).flip
  exact StructureSheafBaseChange.Construction.proper_flat_isPullback_appTop_isIso c a' hc H.flip

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.CoverModificationSections.Construction
