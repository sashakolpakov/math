import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Family Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FamilyComparison

noncomputable section

/-! Compare polarization biextensions after an isomorphism of the abelian family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}

/-- On each fiber, the transported biextension map is the original map after the
product of the induced family isomorphisms. -/
theorem polarizationBiextensionMap_familyTransport (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (s : T ⟶ S) :
    FiberComparison.polarizationBiextensionMap (D.familyTransport e) (e.inv ≫ p) s ≫
        (𝟙 D.abelian.scheme ⊗ₘ e.inv).left =
      ((Over.pullback s).map e.inv ⊗ₘ (Over.pullback s).map e.inv).left ≫
        FiberComparison.polarizationBiextensionMap D p s := by
  let X := (B.pullback s).scheme
  let Y := (A.pullback s).scheme
  let q : (X ⊗ X).left ⟶ (D.abelian.scheme ⊗ B.scheme).left :=
    FiberComparison.polarizationBiextensionMap (D.familyTransport e) (e.inv ≫ p) s
  let r : (D.abelian.scheme ⊗ B.scheme).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    (𝟙 D.abelian.scheme ⊗ₘ e.inv).left
  let t : (Y ⊗ Y).left ⟶ (D.abelian.scheme ⊗ A.scheme).left :=
    FiberComparison.polarizationBiextensionMap D p s
  let a : X.left ⟶ Y.left := ((Over.pullback s).map e.inv).left
  let a₂ : (X ⊗ X).left ⟶ (Y ⊗ Y).left :=
    ((Over.pullback s).map e.inv ⊗ₘ (Over.pullback s).map e.inv).left
  let b : X.left ⟶ B.scheme.left := pullback.fst B.scheme.hom s
  let c : Y.left ⟶ A.scheme.left := pullback.fst A.scheme.hom s
  have hac : a ≫ c = b ≫ e.inv.left := Pullback.Comparisons.overPullback_map_left_fst e.inv s
  change q ≫ r = a₂ ≫ t
  apply Over.tensorObj_ext
  · have hrf : r ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst D.abelian.scheme.hom B.scheme.hom := by
      exact (Over.tensorHom_left_fst _ _ _ _).trans (Category.comp_id _)
    have hqf : q ≫ pullback.fst D.abelian.scheme.hom B.scheme.hom =
        pullback.fst X.hom X.hom ≫ b ≫ (e.inv.left ≫ p.left) :=
      FiberComparison.polarizationBiextensionMap_fst (D.familyTransport e) (e.inv ≫ p) s
    have htf : t ≫ pullback.fst D.abelian.scheme.hom A.scheme.hom =
        pullback.fst Y.hom Y.hom ≫ c ≫ p.left := FiberComparison.polarizationBiextensionMap_fst D p s
    have haf : a₂ ≫ pullback.fst Y.hom Y.hom = pullback.fst X.hom X.hom ≫ a :=
      Over.tensorHom_left_fst _ _ _ _
    simp only [Category.assoc, hrf, hqf, htf, reassoc_of% haf, reassoc_of% hac]
  · have hrs : r ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd D.abelian.scheme.hom B.scheme.hom ≫ e.inv.left :=
      Over.tensorHom_left_snd _ _ _ _
    have hqs : q ≫ pullback.snd D.abelian.scheme.hom B.scheme.hom =
        pullback.snd X.hom X.hom ≫ b :=
      FiberComparison.polarizationBiextensionMap_snd (D.familyTransport e) (e.inv ≫ p) s
    have hts : t ≫ pullback.snd D.abelian.scheme.hom A.scheme.hom =
        pullback.snd Y.hom Y.hom ≫ c := FiberComparison.polarizationBiextensionMap_snd D p s
    have has : a₂ ≫ pullback.snd Y.hom Y.hom = pullback.snd X.hom X.hom ≫ a :=
      Over.tensorHom_left_snd _ _ _ _
    simp only [Category.assoc, hrs, reassoc_of% hqs, hts, reassoc_of% has, hac]

/-- The actual module sheaves in the transported Poincare formula are isomorphic. -/
def polarizationBiextensionFamilyIso (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (s : T ⟶ S) :
    (PolarizationData.polarizationBiextensionAt (D.familyTransport e) (e.inv ≫ p) s).sheaf ≅
      (Line.Bundles.LineBundle.pullback
        ((Over.pullback s).map e.inv ⊗ₘ (Over.pullback s).map e.inv).left
        (PolarizationData.polarizationBiextensionAt D p s)).sheaf :=
  (Scheme.Modules.pullbackComp
    (FiberComparison.polarizationBiextensionMap (D.familyTransport e) (e.inv ≫ p) s)
    (𝟙 D.abelian.scheme ⊗ₘ e.inv).left).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackCongr
        (polarizationBiextensionMap_familyTransport D p e s)).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackComp
        ((Over.pullback s).map e.inv ⊗ₘ (Over.pullback s).map e.inv).left
        (FiberComparison.polarizationBiextensionMap D p s)).symm.app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FamilyComparison
