import OAI.RepresentationTheory.Theta.Geometric.Normalized.DifferenceTranslation
import OAI.RepresentationTheory.Theta.Geometric.Normalized.PullbackComposition

/-! # Difference Translation Cocycle -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferenceTranslationCocycle

noncomputable section

/-! The zero-axis-normalized difference translations satisfy the
actual algebraic composition law. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def normalizedDifferenceTranslation (p : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme)
    (hp : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left).sheaf ≅ L.sheaf)) :
    ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf :=
  (Normalized.DifferenceTranslation.existsUnique_normalized_difference_translation A L p hp e).choose

theorem normalizedDifferenceTranslation_normalized (p : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme)
    (hp : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left).sheaf ≅ L.sheaf)) :
    (Scheme.Modules.pullback (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).mapIso
      (normalizedDifferenceTranslation A L e p hp) ≪≫ e =
        Normalized.DifferenceTranslation.differenceTranslationNormalization A L p e :=
  Iso.ext (Normalized.DifferenceTranslation.existsUnique_normalized_difference_translation A L p hp e).choose_spec.1

theorem normalizedDifferenceTranslation_comp
    (p q : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme)
    (hp : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left).sheaf ≅ L.sheaf))
    (hq : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme q).left).sheaf ≅ L.sheaf))
    (hpq : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme (p * q)).left).sheaf ≅ L.sheaf)) :
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_comp A.scheme p q))).app
        (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf).symm ≪≫
      Normalized.PullbackComposition.composePullbackIso (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left
        (DifferenceBundleTranslation.groupTranslation A.scheme q ⊗ₘ 𝟙 A.scheme).left
        (normalizedDifferenceTranslation A L e p hp) (normalizedDifferenceTranslation A L e q hq) =
      normalizedDifferenceTranslation A L e (p * q) hpq := by
  let i := (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left
  let f := (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left
  let h := (DifferenceBundleTranslation.groupTranslation A.scheme q ⊗ₘ 𝟙 A.scheme).left
  let a := (DifferenceBundleTranslation.groupTranslation A.scheme p).left
  let b := (DifferenceBundleTranslation.groupTranslation A.scheme q).left
  have h₁ : a ≫ i = i ≫ f :=
    (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_zeroSlice A.scheme p)).symm
  have h₂ : b ≫ i = i ≫ h :=
    (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_zeroSlice A.scheme q)).symm
  have h₃ : (a ≫ b) ≫ i = i ≫ (f ≫ h) := by
    rw [Category.assoc, h₂, ← Category.assoc a, h₁, Category.assoc]
  have hn := Normalized.PullbackComposition.composePullbackIso_normalized f h i a b h₁ h₂ h₃
    (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf e
    (normalizedDifferenceTranslation A L e p hp) (normalizedDifferenceTranslation A L e q hq)
    (normalizedDifferenceTranslation_normalized A L e p hp)
    (normalizedDifferenceTranslation_normalized A L e q hq)
  have hc := Normalized.PullbackComposition.pullbackSquareFrame_congr
    (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_comp A.scheme p q)) i
    (congrArg Over.Hom.left (DifferenceBundleTranslation.groupTranslation_mul A.scheme p q)) h₃
    (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_zeroSlice A.scheme (p * q))).symm
    (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf e
  have hn' := hn.trans hc
  apply (Normalized.DifferenceTranslation.existsUnique_normalized_difference_translation A L (p * q) hpq e).choose_spec.2
  suffices H : (Scheme.Modules.pullback i).mapIso
      (((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (DifferenceBundleTranslation.firstTranslation_comp A.scheme p q))).app
        (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf).symm ≪≫
        Normalized.PullbackComposition.composePullbackIso f h (normalizedDifferenceTranslation A L e p hp)
          (normalizedDifferenceTranslation A L e q hq)) ≪≫ e =
      Normalized.DifferenceTranslation.differenceTranslationNormalization A L (p * q) e by
    exact congrArg Iso.hom H
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rw [hn']
  simp only [← Iso.trans_assoc, ← Functor.mapIso_trans, Iso.symm_self_id,
    Functor.mapIso_refl, Iso.refl_trans]
  rfl

theorem normalizedDifferenceTranslation_comp_eq
    (p q r : Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.scheme) (hr : p * q = r)
    (hp : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme p).left).sheaf ≅ L.sheaf))
    (hq : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme q).left).sheaf ≅ L.sheaf))
    (hrL : Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme r).left).sheaf ≅ L.sheaf))
    (ht : (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left ≫
      (DifferenceBundleTranslation.groupTranslation A.scheme q ⊗ₘ 𝟙 A.scheme).left =
      (DifferenceBundleTranslation.groupTranslation A.scheme r ⊗ₘ 𝟙 A.scheme).left) :
    ((Scheme.Modules.pullbackCongr ht).app (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf).symm ≪≫
      Normalized.PullbackComposition.composePullbackIso (DifferenceBundleTranslation.groupTranslation A.scheme p ⊗ₘ 𝟙 A.scheme).left
        (DifferenceBundleTranslation.groupTranslation A.scheme q ⊗ₘ 𝟙 A.scheme).left
        (normalizedDifferenceTranslation A L e p hp) (normalizedDifferenceTranslation A L e q hq) =
      normalizedDifferenceTranslation A L e r hrL := by
  subst r
  exact normalizedDifferenceTranslation_comp A L e p q hp hq hrL

end

end OAI.RepresentationTheory.Theta.Geometric.DifferenceTranslationCocycle
