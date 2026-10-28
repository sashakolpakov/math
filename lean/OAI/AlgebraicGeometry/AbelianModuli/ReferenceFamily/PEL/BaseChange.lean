import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual base change of PEL families, with the action, Rosati
conjugation, Lie signature, polarization, and prescribed level retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {T U : Over (Spec (.of K))}

def PEL.Objects.PELObject.pullback (A : PEL.Objects.PELObject P iota N U) (f : T ⟶ U) : PEL.Objects.PELObject P iota N T where
  polarized := A.polarized.pullback f.left
  action := A.action.pullback f.left
  rosati := ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati f.left
  lieRanks := PEL.Objects.HasPrescribedLieRanks.pullback A.polarized.abelian A.action A.lieRanks f

def PEL.Objects.PELIso.pullback {A B : PEL.Objects.PELObject P iota N U} (e : PEL.Objects.PELIso A B) (f : T ⟶ U) :
    PEL.Objects.PELIso (A.pullback f) (B.pullback f) where
  polarized := e.polarized.pullback f.left
  action a := ((Over.pullback f.left).map_comp (A.action.map a) e.polarized.abelian.hom).symm.trans
    ((congrArg (fun q => (Over.pullback f.left).map q) (e.action a)).trans
      ((Over.pullback f.left).map_comp e.polarized.abelian.hom (B.action.map a)))

/-- The constructed pullback has the exact comparison demanded by the
fine PEL moduli property. -/
def Models.PELPullbackIso.canonical (A : PEL.Objects.PELObject P iota N U) (f : T ⟶ U) :
    Models.PELPullbackIso A (A.pullback f) f where
  abelian := Iso.refl _
  dual := Iso.refl _
  abelianGroup := inferInstanceAs (IsMonHom (𝟙 (A.polarized.abelian.pullback f.left).scheme))
  dualGroup := inferInstanceAs (IsMonHom (𝟙 (A.polarized.dual.abelian.pullback f.left).scheme))
  polarization := (Category.comp_id _).trans (Category.id_comp _).symm
  poincare := by
    change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((𝟙 (A.polarized.dual.abelian.pullback f.left).scheme ⊗ₘ
        𝟙 (A.polarized.abelian.pullback f.left).scheme).left ≫
          HilbertConstruction.PolarizationData.poincareBaseChangeMap A.polarized.dual f.left)
        (HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare) = _
    rw [tensorHom_id, id_whiskerRight]
    change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 _ ≫ HilbertConstruction.PolarizationData.poincareBaseChangeMap A.polarized.dual f.left)
      (HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare) = _
    rw [Category.id_comp, HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap]
    rfl
  level _ _ := Category.comp_id _
  action _ := (Category.comp_id _).trans (Category.id_comp _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
