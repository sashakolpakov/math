import OAI.ArithmeticGeometry.Models.SpreadingOut.ProperAmbient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.Models

/-! # Generic Closed Models -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericClosedModels

noncomputable section

/-! Schematic closure constructs a proper model while retaining its
actual closed embedding in the chosen proper ambient scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem closed_generic_model_with_embedding {S T : Scheme}
    [IsLocallyNoetherian S] (g : T ⟶ S) [IsPreimmersion g] [QuasiCompact g]
    (P : Over S) [IsProper P.hom] (X : Over T)
    (i : X ⟶ (Over.pullback g).obj P) [IsClosedImmersion i.left] :
    ∃ (M : Over S) (j : M ⟶ P),
      IsClosedImmersion j.left ∧ IsProper M.hom ∧
        ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism M.hom ∧
        ∃ e : (Over.pullback g).obj M ≅ X, e.hom ≫ i = (Over.pullback g).map j := by
  let p := pullback.fst P.hom g
  let f := i.left ≫ p
  let M : Over S := Over.mk (f.imageι ≫ P.hom)
  let j : M ⟶ P := Over.homMk f.imageι rfl
  have hj : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion f.imageι)
  have hproper : IsProper M.hom := inferInstanceAs (IsProper (f.imageι ≫ P.hom))
  have hfp : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism M.hom :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have hcart : IsPullback f.toImage X.hom M.hom g := by
    have hc := (ArithmeticGeometry.Models.SpreadingOut.SchematicClosure.Construction.schematicClosure_isPullback i.left p).flip
    have h := hc.paste_vert (IsPullback.of_hasPullback P.hom g)
    have hi : i.left ≫ pullback.snd P.hom g = X.hom := i.w
    rw [hi] at h
    exact h
  let e : (Over.pullback g).obj M ≅ X :=
    Over.isoMk hcart.isoPullback.symm hcart.isoPullback_inv_snd
  refine ⟨M, j, hj, hproper, hfp, e, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (e.hom.left ≫ i.left) ≫ pullback.fst P.hom g = _
    calc
      _ = e.hom.left ≫ f := Category.assoc _ _ _
      _ = (e.hom.left ≫ f.toImage) ≫ f.imageι := by rw [Category.assoc, f.toImage_imageι]
      _ = pullback.fst M.hom g ≫ f.imageι :=
        congrArg (fun a => a ≫ f.imageι) hcart.isoPullback_inv_fst
      _ = _ := (pullback.lift_fst _ _ _).symm
  · exact (e.hom ≫ i).w.trans ((Over.pullback g).map j).w.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericClosedModels
