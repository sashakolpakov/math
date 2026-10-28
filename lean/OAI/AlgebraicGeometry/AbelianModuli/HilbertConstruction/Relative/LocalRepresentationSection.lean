import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.RepresentableOpenGlueData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GluedSheafSections

/-! # Local Representation Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentationSection

noncomputable section

/-! The universal elements on relatively representable open charts glue to a universal element on their constructed relative scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {ι : Type u} {X : ι → Over S} {f : ∀ i, yoneda.obj (X i) ⟶ F}
variable (hf : ∀ i, (RepresentableOpenGlueData.relativeOpenImmersions S).presheaf (f i))

def relativeLocalRepresentationScheme : Over S :=
  SchemeGluing.relativeGlued (RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf) (RepresentableOpenGlueData.relativeRepresentableOpenGlueData_open hf)

def relativeLocalRepresentationInclusion (i : ι) : X i ⟶ relativeLocalRepresentationScheme hf :=
  SchemeGluing.relativeGlueInclusion (RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf) (RepresentableOpenGlueData.relativeRepresentableOpenGlueData_open hf) i

theorem relativeLocalRepresentation_overlap (i j : ι) :
    yoneda.map ((RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf).f i j) ≫ f i =
      yoneda.map ((RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf).t i j ≫
        (RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf).f j i) ≫ f j := by
  exact ((hf i).rep.isPullback' (f j)).w.trans
    (congrArg (fun z => yoneda.map z ≫ f j)
      (Functor.relativelyRepresentable.symmetry_fst (hf i).rep (hf j).rep).symm)

theorem relativeLocalRepresentation_existsUnique_section
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) :
    ∃! s : F.obj (.op (relativeLocalRepresentationScheme hf)),
      ∀ i, F.map (relativeLocalRepresentationInclusion hf i).op s = yonedaEquiv (f i) := by
  apply GluedSheafSections.relativeGlued_existsUnique_sheafSection (RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf)
    (RepresentableOpenGlueData.relativeRepresentableOpenGlueData_open hf) F hF (fun i => yonedaEquiv (f i))
  intro i j
  have h := congrArg yonedaEquiv (relativeLocalRepresentation_overlap hf i j)
  exact (yonedaEquiv_naturality (f i) ((RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf).f i j)).trans
    (h.trans (yonedaEquiv_naturality (f j) ((RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf).t i j ≫
      (RepresentableOpenGlueData.relativeRepresentableOpenGlueData hf).f j i)).symm)

def relativeLocalRepresentationSection (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) :
    F.obj (.op (relativeLocalRepresentationScheme hf)) :=
  (relativeLocalRepresentation_existsUnique_section hf hF).choose

theorem relativeLocalRepresentationSection_restrict
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) (i : ι) :
    F.map (relativeLocalRepresentationInclusion hf i).op (relativeLocalRepresentationSection hf hF) =
      yonedaEquiv (f i) :=
  (relativeLocalRepresentation_existsUnique_section hf hF).choose_spec.1 i

def relativeLocalRepresentationMap (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) :
    yoneda.obj (relativeLocalRepresentationScheme hf) ⟶ F :=
  yonedaEquiv.symm (relativeLocalRepresentationSection hf hF)

theorem relativeLocalRepresentationMap_chart
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F) (i : ι) :
    yoneda.map (relativeLocalRepresentationInclusion hf i) ≫ relativeLocalRepresentationMap hf hF = f i := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality]
  exact (congrArg (F.map (relativeLocalRepresentationInclusion hf i).op)
    (yonedaEquiv.apply_symm_apply (relativeLocalRepresentationSection hf hF))).trans
    (relativeLocalRepresentationSection_restrict hf hF i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalRepresentationSection
