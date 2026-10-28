import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantInverseImageNaturality
import OAI.AlgebraicGeometry.Cohomology.GlobalSections

/-! # Global Sheaf Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalSheafPullback

noncomputable section

/-! # Genuine pullback on original global sections

The adjunction unit gives actual pullback of global sections. Evaluation at
the original constant integer section one commutes with this pullback.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

section AdjointTransport

variable {C D : Type*} [Category* C] [Category* D]
  {F F' : C ⥤ D} {G : D ⥤ C}

/-- Canonical transport between left adjoints preserves their original Hom equivalences. -/
theorem homEquiv_leftAdjointUniq_inv_comp (a₁ : F ⊣ G) (a₂ : F' ⊣ G)
    (A : C) (B : D) (g : F.obj A ⟶ B) :
    a₂.homEquiv A B ((a₁.leftAdjointUniq a₂).inv.app A ≫ g) =
      a₁.homEquiv A B g := by
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact (a₁.homEquiv_unit A B g).symm

end AdjointTransport

section CompositeTransport

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {L : A ⥤ B} {R : B ⥤ A} {F : B ⥤ C} {P : C ⥤ B} {L' : A ⥤ C}

/-- Constant-source transport and the genuine adjunction unit give the same section map. -/
theorem constantHomAdjunctionInverseImage (aL : L ⊣ R) (aF : F ⊣ P)
    (aL' : L' ⊣ P ⋙ R) (T : A) (K : B) (g : L.obj T ⟶ K) :
    aL'.homEquiv T (F.obj K)
        (((aL.comp aF).leftAdjointUniq aL').inv.app T ≫ F.map g) =
      aL.homEquiv T K g ≫ R.map (aF.unit.app K) := by
  have h := homEquiv_leftAdjointUniq_inv_comp (aL.comp aF) aL'
    T (F.obj K) (F.map g)
  rw [Adjunction.comp_homEquiv] at h
  change _ = aL.homEquiv T _ (aF.homEquiv _ _ (F.map g)) at h
  have hg : aF.homEquiv _ _ (F.map g) = g ≫ aF.unit.app K := by
    change aF.unit.app _ ≫ P.map (F.map g) = g ≫ aF.unit.app K
    exact (aF.unit.naturality g).symm
  exact h.trans ((congrArg (aL.homEquiv T _) hg).trans
    (aL.homEquiv_naturality_right g (aF.unit.app K)))

end CompositeTransport

variable {X Y : Over (Spec (.of ℂ))}

/-- The actual adjunction unit, evaluated on the original top open. -/
def originalGlobalSectionsInverseImageNat (f : X ⟶ Y) :
    AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)) ⟶
      AnalyticInverseImage.originalAnalyticSheafInverseImage f ⋙
        AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) where
  app K := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).unit.app K).hom.app (Opposite.op ⊤)
  naturality {K L} g := by
    exact congrArg (fun q => q.hom.app (Opposite.op ⊤))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).unit.naturality g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual pullback of global sections agrees with evaluation of actual constant-source maps. -/
theorem originalIntegerConstantHomGlobalSections_inverseImage (f : X ⟶ Y)
    (K : ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)
    (g : (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj
      (AddCommGrpCat.of ℤ) ⟶ K) :
    Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections
        ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).obj K)
        (((AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).inv.app (AddCommGrpCat.of ℤ)) ≫
          (AnalyticInverseImage.originalAnalyticSheafInverseImage f).map g) =
      (originalGlobalSectionsInverseImageNat f).app K
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantHomAddEquivGlobalSections K g) := by
  let aY := constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))
    AddCommGrpCat isTerminalTop
  let aX := constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
    AddCommGrpCat isTerminalTop
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (DeRhamPresheafPullback.originalAnalyticSchemeMap f)
  have h := constantHomAdjunctionInverseImage aY a aX (AddCommGrpCat.of ℤ) K g
  change ((aX.homEquiv (AddCommGrpCat.of ℤ) _)
      ((AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).inv.app (AddCommGrpCat.of ℤ) ≫
        (AnalyticInverseImage.originalAnalyticSheafInverseImage f).map g)) 1 =
    ((a.unit.app K).hom.app (Opposite.op ⊤)) ((aY.homEquiv (AddCommGrpCat.of ℤ) _ g) 1)
  exact congrArg (fun q : AddCommGrpCat.of ℤ ⟶
      ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).obj K).presheaf.obj (Opposite.op ⊤) =>
    q.hom (1 : ℤ)) h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.GlobalSheafPullback
