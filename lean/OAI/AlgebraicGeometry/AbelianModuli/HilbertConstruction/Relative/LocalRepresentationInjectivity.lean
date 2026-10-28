import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentationSection
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Local Representation Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentationInjectivity

noncomputable section

/-! The map from the glued relative charts to the original sheaf is injective on every test. Equality is checked on the common refinement of the pulled-back chart covers. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {ι : Type u} {X : ι → Over S} {f : ∀ i, yoneda.obj (X i) ⟶ F}
variable (hf : ∀ i, (RepresentableOpenGlueData.relativeOpenImmersions S).presheaf (f i))

theorem relativeLocalRepresentation_comp_eq {T : Over S} {i j : ι}
    (a : T ⟶ X i) (b : T ⟶ X j) (h : yoneda.map a ≫ f i = yoneda.map b ≫ f j) :
    a ≫ LocalRepresentationSection.relativeLocalRepresentationInclusion hf i = b ≫ LocalRepresentationSection.relativeLocalRepresentationInclusion hf j := by
  let D := RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf
  have : HasMulticoequalizer D.diagram := SchemeGluing.relativeGlueData_hasColimit D
    (RepresentableOpenGlueData.relativeRepresentableOpenGlueData_open hf)
  let l := (hf i).rep.lift' a b h
  have hi : l ≫ (hf i).rep.fst' (f j) = a := (hf i).rep.lift'_fst a b h
  have hj : l ≫ (hf i).rep.snd (f j) = b := (hf i).rep.lift'_snd a b h
  have hc : (hf i).rep.fst' (f j) ≫ D.ι i = (hf i).rep.snd (f j) ≫ D.ι j :=
    (D.glue_condition i j).symm.trans
      ((Category.assoc ((hf i).rep.symmetry (hf j).rep) ((hf j).rep.fst' (f i)) (D.ι j)).symm.trans
        (congrArg (fun z => z ≫ D.ι j)
          (Functor.relativelyRepresentable.symmetry_fst (hf i).rep (hf j).rep)))
  exact (congrArg (fun z => z ≫ D.ι i) hi.symm).trans
    ((Category.assoc l ((hf i).rep.fst' (f j)) (D.ι i)).trans
      ((congrArg (fun z => l ≫ z) hc).trans
        ((Category.assoc l ((hf i).rep.snd (f j)) (D.ι j)).symm.trans
          (congrArg (fun z => z ≫ D.ι j) hj))))

theorem relativeLocalRepresentationMap_injective
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) (T : Over S) :
    Function.Injective ((LocalRepresentationSection.relativeLocalRepresentationMap hf hF).app (.op T)) := by
  let G := LocalRepresentationSection.relativeLocalRepresentationScheme hf
  let α := LocalRepresentationSection.relativeLocalRepresentationMap hf hF
  let J := Scheme.zariskiTopology.over S
  let R := Sieve.ofArrows X (LocalRepresentationSection.relativeLocalRepresentationInclusion hf)
  have hR : R ∈ J G := GluedSheafSections.relativeGlueInclusion_sieve_mem (RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf)
    (RepresentableOpenGlueData.relativeRepresentableOpenGlueData_open hf)
  have hG : Presieve.IsSheaf J (yoneda.obj G) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  intro p q hpq
  have hm : R.pullback p ⊓ R.pullback q ∈ J T :=
    J.intersection_covering (J.pullback_stable p hR) (J.pullback_stable q hR)
  apply (hG _ hm).isSeparatedFor.ext
  rintro V γ ⟨⟨W₁, a, _, ⟨i⟩, ha⟩, ⟨W₂, b, _, ⟨j⟩, hb⟩⟩
  change γ ≫ p = γ ≫ q
  rw [← ha, ← hb]
  apply relativeLocalRepresentation_comp_eq hf a b
  have hγ : α.app (.op V) (γ ≫ p) = α.app (.op V) (γ ≫ q) :=
    (NatTrans.naturality_apply α γ.op p).trans
      ((congrArg (F.map γ.op) hpq).trans (NatTrans.naturality_apply α γ.op q).symm)
  apply yonedaEquiv.injective
  have hi := LocalRepresentationSection.relativeLocalRepresentationMap_chart hf hF i
  have hj := LocalRepresentationSection.relativeLocalRepresentationMap_chart hf hF j
  rw [← hi, ← hj, ← Category.assoc, ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp]
  simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  exact (congrArg (fun z => α.app (.op V) z) ha).trans
    (hγ.trans (congrArg (fun z => α.app (.op V) z) hb).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentationInjectivity
