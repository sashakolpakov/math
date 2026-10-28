import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedPolarizedPoincareCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.PreservationRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationOpenLocality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Noetherian Target PEL Recovery -/

namespace OAI.RepresentationTheory.Hecke.NoetherianTargetPELRecovery.OrdinaryCharacterIntrinsic

noncomputable section

/-! Recover a complete PEL comparison to a pullback of an actual
locally Noetherian family. The other family and the test base are
arbitrary. The canonical dual and its Poincare comparison are
constructed; local comparisons supply the remaining equations on a
given global group isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationOpenLocality

theorem poincare_comparison_to_noetherian_pullback
    {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (e : B.abelian.scheme ≅ (A.pullback f).abelian.scheme) [IsMonHom e.hom] :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((B.dual.familyComparisonIso (A.pullback f).dual e).hom ⊗ₘ e.hom).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (A.pullback f).dual.poincare) = AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare := by
  let D := B.dual
  let E := (A.pullback f).dual
  let d := (D.familyComparisonIso E e).hom
  let l := 𝟙 D.abelian.scheme ⊗ₘ e.hom
  have h := A.baseChanged_uniqueDualIso_poincare_class f (D.familyTransport e) E
  change AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 (A.pullback f).abelian.scheme).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) =
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.inv).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) at h
  have hl : l ≫ (d ⊗ₘ 𝟙 (A.pullback f).abelian.scheme) = d ⊗ₘ e.hom := by
    simpa only [l, id_tensorHom, tensorHom_id] using (tensorHom_def' d e.hom).symm
  have hr : l ≫ (𝟙 D.abelian.scheme ⊗ₘ e.inv) = 𝟙 _ := by simp [l]
  have H := congrArg (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass l.left) h
  rw [← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    ← Over.comp_left, ← Over.comp_left, hl, hr, Over.id_left, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at H
  exact H

def polarized_comparison_to_noetherian_pullback_of_local
    {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (f : T ⟶ S)
    (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (e : B.abelian.scheme ≅ (A.pullback f).abelian.scheme) [IsMonHom e.hom]
    (C : T.OpenCover)
    (u : ∀ j, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (B.pullback (C.f j)) ((A.pullback f).pullback (C.f j)))
    (hu : ∀ j, (u j).abelian.hom = (Over.pullback (C.f j)).map e.hom) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso B (A.pullback f) := by
  let d := B.dual.familyComparisonIso (A.pullback f).dual e
  have hD := poincare_comparison_to_noetherian_pullback A f B e
  have hd (j) : (u j).dual.hom = (Over.pullback (C.f j)).map d.hom := by
    apply (u j).dual_hom_eq_of_poincare
    exact (congrArg (fun a => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((Over.pullback (C.f j)).map d.hom ⊗ₘ a).left
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((A.pullback f).dual.pullback (C.f j)).poincare)) (hu j)).trans
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange.poincareCompatibility_pullback B.dual (A.pullback f).dual d.hom e.hom hD (C.f j))
  have hgroup : IsMonHom d.hom := by
    apply AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection.isMonHom_of_open_base_cover C
    intro j
    rw [← hd j]
    exact (u j).dualGroup
  have hlocal := fun j => AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullback_preservation_conditions B
    (A.pullback f) e.hom d.hom hD (C.f j) (u j) (hu j)
  exact {
    abelian := e
    dual := d
    abelianGroup := inferInstance
    dualGroup := hgroup
    polarization := AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection.over_hom_ext_of_open_base_cover C _ _ (fun j => (hlocal j).1)
    poincare := hD
    level := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationOpenLocality.fullLevel_preserves_of_openCover B.level (A.pullback f).level e.hom C
      (fun j => (hlocal j).2)
  }

theorem fullPEL_comparison_to_noetherian_pullback_of_local
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S T : Scheme.{0}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N S) (f : T ⟶ S) (B : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.PolarizedActionData E g δ N T)
    (e : B.polarized.abelian.scheme ≅ (A.pullback f).polarized.abelian.scheme) [IsMonHom e.hom]
    (C : T.OpenCover)
    (u : ∀ j, AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (B.pullback (C.f j)) ((A.pullback f).pullback (C.f j)))
    (hu : ∀ j, (u j).polarized.abelian.hom = (Over.pullback (C.f j)).map e.hom) :
    ∃ v : AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso B (A.pullback f), v.polarized.abelian = e := by
  let v := polarized_comparison_to_noetherian_pullback_of_local A.polarized f B.polarized e C
    (fun j => (u j).polarized) hu
  have he : v.abelian = e := rfl
  have haction (a : NumberField.RingOfIntegers E) :
      B.action.map a ≫ v.abelian.hom = v.abelian.hom ≫ (A.pullback f).action.map a := by
    rw [he]
    apply AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseGroupReflection.over_hom_ext_of_open_base_cover C
    intro j
    rw [Functor.map_comp, Functor.map_comp, ← hu j]
    exact (u j).action a
  exact ⟨⟨v, haction⟩, he⟩

end

end OAI.RepresentationTheory.Hecke.NoetherianTargetPELRecovery.OrdinaryCharacterIntrinsic
