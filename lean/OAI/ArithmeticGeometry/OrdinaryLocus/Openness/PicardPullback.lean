import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardEq

/-! # Picard Pullback -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardPullback.Construction

noncomputable section

/-! Contravariant functoriality and descent for Picard groups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def picardPullback {X Y : Scheme.{u}} (f : X ⟶ Y) : PicardEq.Construction.Picard Y →+ PicardEq.Construction.Picard X where
  toFun := Quotient.map
    (fun L ↦ ⟨(Scheme.Modules.pullback f).obj L.sheaf, LineBundle.Construction.isLineBundle_pullback f L.sheaf L.isLineBundle⟩)
    (fun _ _ ⟨e⟩ ↦ ⟨(Scheme.Modules.pullback f).mapIso e⟩)
  map_zero' := Quotient.sound ⟨LineBundle.Construction.pullbackStructureSheafIso f⟩
  map_add' a b := Quotient.inductionOn₂ a b fun L M ↦
    Quotient.sound ⟨LineBundleTensorPullback.Construction.pullbackLineBundleTensorIso f L.isLineBundle M.isLineBundle⟩

theorem picardPullback_class {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    picardPullback f (PicardEq.Construction.lineBundleClass M hM) =
      PicardEq.Construction.lineBundleClass ((Scheme.Modules.pullback f).obj M) (LineBundle.Construction.isLineBundle_pullback f M hM) := rfl

theorem picardPullback_id (X : Scheme.{u}) : picardPullback (𝟙 X) = AddMonoidHom.id (PicardEq.Construction.Picard X) := by
  apply AddMonoidHom.ext
  intro a
  exact Quotient.inductionOn a fun L ↦ Quotient.sound ⟨(Scheme.Modules.pullbackId X).app L.sheaf⟩

theorem picardPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    picardPullback (f ≫ g) = (picardPullback f).comp (picardPullback g) := by
  apply AddMonoidHom.ext
  intro a
  exact Quotient.inductionOn a fun L ↦
    Quotient.sound ⟨((Scheme.Modules.pullbackComp f g).app L.sheaf).symm⟩

theorem picardPullback_injective_of_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) : Function.Injective (picardPullback f) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro L M h
  have he : Nonempty ((Scheme.Modules.pullback f).obj L.sheaf ≅ (Scheme.Modules.pullback f).obj M.sheaf) :=
    Quotient.exact h
  obtain ⟨e⟩ := he
  exact Quotient.sound ⟨LineBundleDescent.Construction.descendLineBundleIso f hf L.isLineBundle M.isLineBundle e⟩

theorem picardPullback_properProduct_injective
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left] :
    Function.Injective (picardPullback (CartesianMonoidalCategory.fst Y X).left) :=
  picardPullback_injective_of_app (CartesianMonoidalCategory.fst Y X).left
    (UniversalGlobalSections.Construction.isIso_properBaseChange_app Y X)

def picardPullbackIso {X Y : Scheme.{u}} (e : X ≅ Y) : PicardEq.Construction.Picard Y ≃+ PicardEq.Construction.Picard X where
  toFun := picardPullback e.hom
  invFun := picardPullback e.inv
  map_add' := (picardPullback e.hom).map_add
  left_inv a := by
    have h := congrArg (fun f : PicardEq.Construction.Picard Y →+ PicardEq.Construction.Picard Y ↦ f a) (picardPullback_comp e.inv e.hom)
    rw [e.inv_hom_id, picardPullback_id] at h
    exact h.symm
  right_inv a := by
    have h := congrArg (fun f : PicardEq.Construction.Picard X →+ PicardEq.Construction.Picard X ↦ f a) (picardPullback_comp e.hom e.inv)
    rw [e.hom_inv_id, picardPullback_id] at h
    exact h.symm

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardPullback.Construction
