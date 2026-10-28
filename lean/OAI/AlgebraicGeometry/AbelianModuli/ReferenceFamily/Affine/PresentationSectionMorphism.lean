import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionSectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.SectionTransport

/-! # Presentation Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism

noncomputable section

/-! Actual affine coefficient maps commuting with an ambient scheme
morphism agree with pullback of the original regular sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

theorem openRange_preimage_of_square {A B X Y : Scheme.{0}}
    (q : A ⟶ B) (i : B ⟶ Y) (j : A ⟶ X) (f : X ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : q ≫ i = j ≫ f) :
    j.opensRange ≤ f ⁻¹ᵁ i.opensRange := by
  rintro x ⟨a, rfl⟩
  refine ⟨q a, ?_⟩
  exact congrArg (fun m : A ⟶ Y => m a) h

theorem affinePresentationRegularSectionEquiv_morphism
    (k : Type) [CommRing k] (B C : CommAlgCat k) (X Y : Over (Spec (.of k)))
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ Y) (j : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ X)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] (f : X ⟶ Y) (q : B →ₐ[k] C)
    (hi : AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ≫ i = j ≫ f)
    (h : j.left.opensRange ≤ f.left ⁻¹ᵁ i.left.opensRange) (a : B) :
    PresentationRegularSections.affinePresentationRegularSectionEquiv k C X j (q a) =
      f.left.appLE i.left.opensRange j.left.opensRange h (PresentationRegularSections.affinePresentationRegularSectionEquiv k B Y i a) := by
  let m := AlgebraAutomorphismNaturality.affineOverAlgHom k B C q
  have hΓ : (Scheme.ΓSpecIso (.of C)).inv (q a) =
      m.left.appTop ((Scheme.ΓSpecIso (.of B)).inv a) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q.toRingHom)) a
  have H := ConcreteCategory.congr_hom (Open.ImmersionSectionMorphism.openImmersionTopSectionIso_morphism m.left i.left j.left f.left
    (congrArg Over.Hom.left hi) h) ((Scheme.ΓSpecIso (.of B)).inv a)
  change (IsOpenImmersion.ΓIsoTop j.left).hom ((Scheme.ΓSpecIso (.of C)).inv (q a)) =
    f.left.appLE i.left.opensRange j.left.opensRange h
      ((IsOpenImmersion.ΓIsoTop i.left).hom ((Scheme.ΓSpecIso (.of B)).inv a))
  rw [hΓ]
  exact H

theorem regularSectionTransport_appLE {X Y : Scheme.{0}} (f : X ⟶ Y)
    {U U' : Y.Opens} {V V' : X.Opens} (hU : U = U') (hV : V = V')
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (s : Γ(Y, U)) :
    Regular.SectionTransport.regularSectionTransport hV (f.appLE U V h s) =
      f.appLE U' V' h' (Regular.SectionTransport.regularSectionTransport hU s) := by
  subst U'
  subst V'
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationSectionMorphism
