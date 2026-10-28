import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Functor

/-! # Whole Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WholeFamily.Hilbert

noncomputable section

/-! A flat proper finitely presented ambient scheme itself gives the
whole native Hilbert family over every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S)
variable [Flat X.hom] [IsProper X.hom] [LocallyOfFinitePresentation X.hom]

theorem isFamily_bot (T : Over S) : Hilbert.Functor.IsFamily X (⊥ : (Hilbert.Functor.ambient X T).IdealSheafData) := by
  let : Flat (Hilbert.Functor.ambientProjection X T) := by
    change Flat (prod.fst : T ⨯ X ⟶ T).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  let : IsProper (Hilbert.Functor.ambientProjection X T) := by
    change IsProper (prod.fst : T ⨯ X ⟶ T).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  let : LocallyOfFinitePresentation (Hilbert.Functor.ambientProjection X T) := by
    change LocallyOfFinitePresentation (prod.fst : T ⨯ X ⟶ T).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  change Flat ((⊥ : (Hilbert.Functor.ambient X T).IdealSheafData).subschemeι ≫ Hilbert.Functor.ambientProjection X T) ∧
    IsProper ((⊥ : (Hilbert.Functor.ambient X T).IdealSheafData).subschemeι ≫ Hilbert.Functor.ambientProjection X T) ∧
    LocallyOfFinitePresentation ((⊥ : (Hilbert.Functor.ambient X T).IdealSheafData).subschemeι ≫ Hilbert.Functor.ambientProjection X T)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def wholeFamily (T : Over S) : Hilbert.Functor.Family X T := ⟨⊥, isFamily_bot X T⟩

theorem wholeFamily_pullback {T U : Over S} (a : T ⟶ U) :
    Hilbert.Functor.pullbackFamily X a (wholeFamily X U) = wholeFamily X T :=
  Subtype.ext (Scheme.IdealSheafData.comap_bot _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WholeFamily.Hilbert
