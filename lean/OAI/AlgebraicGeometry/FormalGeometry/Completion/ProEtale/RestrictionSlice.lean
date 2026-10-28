import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.EtaleRestriction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.Local

/-! # Restriction Slice -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-!
# Completion: local representatives commute with restriction of the base

On a slice over a fixed covering object, composition of base maps is fully
faithful and carries the actual coefficient scheme to the coefficient scheme.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f) (U : Y.ProEt)

/-- Composition is fully faithful after passing to the slice over a fixed site object. -/
def ProEtale.RestrictionSlice.Construction.proEtComposeOverFullyFaithful : (Over.post (X := U) (ProEtale.EtaleRestriction.Construction.proEtCompose f hf)).FullyFaithful where
  preimage {A B} g := Over.homMk (MorphismProperty.Over.homMk g.left.left (by
    have h := congrArg (fun k => k.left) g.w
    have h' := congrArg (fun k => k ≫ U.hom) h
    change (g.left.left ≫ B.hom.left) ≫ U.hom = A.hom.left ≫ U.hom at h'
    simpa only [Category.assoc, MorphismProperty.Over.w] using! h')) (by
      apply MorphismProperty.Over.Hom.ext
      exact congrArg (fun k => k.left) g.w)
  map_preimage g := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl
  preimage_map g := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

/-- Restriction preserves the actual finite coefficient representative in the slice. -/
def ProEtale.RestrictionSlice.Construction.proEtComposeOverCoefficientIso (ℓ n : ℕ) :
    (Over.post (ProEtale.EtaleRestriction.Construction.proEtCompose f hf)).obj (FiniteTorsor.Local.Construction.finiteCoefficientSlice ℓ n U) ≅
      FiniteTorsor.Local.Construction.finiteCoefficientSlice ℓ n ((ProEtale.EtaleRestriction.Construction.proEtCompose f hf).obj U) :=
  Over.isoMk
    (MorphismProperty.Over.isoMk
      (Iso.refl (FiniteTorsor.Local.Construction.finiteCoefficientSlice ℓ n U).left.left)
      (by simp [FiniteTorsor.Local.Construction.finiteCoefficientSlice, ProEtale.EtaleRestriction.Construction.proEtCompose, Category.assoc]))
    (by
      apply MorphismProperty.Over.Hom.ext
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      rfl)

variable {ℓ n : ℕ} (E : FiniteTorsor.App.Construction.FiniteCoefficientExtension ℓ n X)
  (s : E.Fiber ((ProEtale.EtaleRestriction.Construction.proEtCompose f hf).obj U))

/-- The actual local torsor representative also represents the sheaf restricted to the smaller base. -/
def FiniteTorsor.App.Construction.FiniteCoefficientExtension.restrictedLocalRepresentative :
    ((Over.forget U).op ⋙ (ProEtale.EtaleRestriction.Construction.proEtCompose f hf).op ⋙ E.fiberPresheaf).RepresentableBy
      (FiniteTorsor.Local.Construction.finiteCoefficientSlice ℓ n U) := by
  let rep := (E.localRepresentative s).ofIsoObj (ProEtale.RestrictionSlice.Construction.proEtComposeOverCoefficientIso f hf U ℓ n)
  exact {
    homEquiv := (ProEtale.RestrictionSlice.Construction.proEtComposeOverFullyFaithful f hf U).homEquiv.trans rep.homEquiv
    homEquiv_comp g h := by
      change rep.homEquiv ((Over.post (ProEtale.EtaleRestriction.Construction.proEtCompose f hf)).map (g ≫ h)) = _
      rw [CategoryTheory.Functor.map_comp, rep.homEquiv_comp]
      rfl }

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
