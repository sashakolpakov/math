import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections

/-! # Presentation Regular Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections

noncomputable section

/-! The ring of any actual affine presentation identifies with
the original regular sections on its open image. The identification
preserves restrictions and the constants of the original base morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k : Type) [CommRing k] (B : CommAlgCat k) (X : Over (Spec (.of k)))
    (i : EtaleSplittingAt.EtaleSplitting.affineOver k B ⟶ X) [IsOpenImmersion i.left]

def affinePresentationRegularSectionEquiv : B ≃+* Γ(X.left, i.left.opensRange) :=
  ((Scheme.ΓSpecIso (.of B)).symm ≪≫ IsOpenImmersion.ΓIsoTop i.left).commRingCatIsoToRingEquiv

theorem affinePresentationRegularSectionEquiv_constant (c : k) :
    affinePresentationRegularSectionEquiv k B X i (algebraMap k B c) =
      X.left.presheaf.map (homOfLE (show i.left.opensRange ≤ ⊤ from le_top)).op
        (X.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) := by
  have hΓ : (Scheme.ΓSpecIso (.of B)).inv (algebraMap k B c) =
      (Spec.map (CommRingCat.ofHom (algebraMap k B))).appTop ((Scheme.ΓSpecIso (.of k)).inv c) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k B))) c
  have hi := congrArg (fun f : (EtaleSplittingAt.EtaleSplitting.affineOver k B).left ⟶ Spec (.of k) =>
    f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) i.w
  rw [Scheme.Hom.comp_appTop] at hi
  have he : (Scheme.ΓSpecIso (.of B)).inv (algebraMap k B c) =
      i.left.appTop (X.hom.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) := hΓ.trans hi.symm
  change (IsOpenImmersion.ΓIsoTop i.left).hom ((Scheme.ΓSpecIso (.of B)).inv (algebraMap k B c)) = _
  rw [he]
  exact Open.ImmersionGlobalSections.openImmersionTopSection_global i.left _

variable (C : CommAlgCat k) (j : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ X) [IsOpenImmersion j.left]

theorem affinePresentationRegularSectionEquiv_natural (q : B →ₐ[k] C)
    (hi : AlgebraAutomorphismNaturality.affineOverAlgHom k B C q ≫ i = j) (h : j.left.opensRange ≤ i.left.opensRange) (a : B) :
    affinePresentationRegularSectionEquiv k C X j (q a) =
      X.left.presheaf.map (homOfLE h).op (affinePresentationRegularSectionEquiv k B X i a) := by
  let f := AlgebraAutomorphismNaturality.affineOverAlgHom k B C q
  have hΓ : (Scheme.ΓSpecIso (.of C)).inv (q a) =
      f.left.appTop ((Scheme.ΓSpecIso (.of B)).inv a) :=
    ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q.toRingHom)) a
  have hs := ConcreteCategory.congr_hom (Open.ImmersionGlobalSections.openImmersionTopSectionIso_natural f.left i.left j.left
    (congrArg (fun g => g.left) hi) h) ((Scheme.ΓSpecIso (.of B)).inv a)
  change (IsOpenImmersion.ΓIsoTop j.left).hom ((Scheme.ΓSpecIso (.of C)).inv (q a)) =
    X.left.presheaf.map (homOfLE h).op ((IsOpenImmersion.ΓIsoTop i.left).hom ((Scheme.ΓSpecIso (.of B)).inv a))
  rw [hΓ]
  exact hs

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections
