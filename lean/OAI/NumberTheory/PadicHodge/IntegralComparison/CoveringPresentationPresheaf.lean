import OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ComplexAssemblyRestriction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution

/-! # Covering Presentation Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationPresheaf

noncomputable section

/-! Tuples of actual maps into covering objects give the canonical local free resolution of constant coefficients. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] {ι : Type v} (F : ι → C)

def presentations : Cᵒᵖ ⥤ Type (max u v) where
  obj U := ULift.{u} (Σ i, U.unop ⟶ F i)
  map α := ↾fun x => ⟨⟨x.down.1, α.unop ≫ x.down.2⟩⟩
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact Sigma.ext rfl (heq_of_eq (Category.id_comp _))
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact Sigma.ext rfl (heq_of_eq (Category.assoc _ _ _))

instance restricted_nonempty (i : ι) (U : (Over (F i))ᵒᵖ) :
    Nonempty (((Over.forget (F i)).op ⋙ presentations F).obj U) :=
  ⟨⟨⟨i, U.unop.hom⟩⟩⟩

variable (R : Type (max u v)) [CommRing R]

theorem restricted_rawAugmentation (i : ι) :
    QuasiIso ((((Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj (Over.forget (F i)).op).mapHomologicalComplex
      (.down ℕ)).map
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.rawAugmentation R (presentations F))) := by
  apply ComplexAssemblyRestriction.quasiIso
  intro U
  let : Nonempty ((presentations F).obj ((Over.forget (F i)).op.obj U)) := restricted_nonempty F i U
  exact AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra.NonemptyCechNerve.augmentation_quasiIso R
    ((presentations F).obj ((Over.forget (F i)).op.obj U))

theorem restricted_augmentation (i : ι) :
    QuasiIso ((((Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj (Over.forget (F i)).op).mapHomologicalComplex
      (.down ℕ)).map
        (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.augmentation R (presentations F))) := by
  let T := ((Functor.whiskeringLeft _ _ (ModuleCat.{max u v} R)).obj (Over.forget (F i)).op).mapHomologicalComplex
    (.down ℕ)
  let h : QuasiIso (T.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.rawAugmentation R (presentations F))) :=
    restricted_rawAugmentation F R i
  change QuasiIso (T.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.rawAugmentation R (presentations F) ≫
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution.targetIso R (presentations F)).hom))
  rw [T.map_comp]
  exact quasiIso_comp _ _ (hφ := h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationPresheaf
