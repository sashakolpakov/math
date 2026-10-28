import OAI.AlgebraicGeometry.Comparison.Betti.Godement.PushforwardBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.Godement.AdditiveImage
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column

/-! # Cech Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Godement.CechImage

noncomputable section

/-! The original Čech comparison induces a quasi-isomorphism on global sections of the canonical Godement totals. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} [Finite ι] (U : ι → Opens X)

local instance godementCechDirectImagePush : (TopologicalSheafPullback.sheafDirectImage f).Additive :=
  TopologicalSheafPullback.sheafDirectImageAdditive f

local instance godementCechDirectImageAbPush :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

variable {K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ}
  {L : CochainComplex (ConstantSheafSections.ComplexSheaves Y) ℕ}
  (α : K ⟶ ((TopologicalSheafPullback.sheafDirectImage f).mapHomologicalComplex (.up ℕ)).obj L)

omit [Finite ι] in
theorem godementDirectImageTotalMap_additiveAugmentation :
    Cech.additiveGodementTotalAugmentation K ≫ AdditiveImage.additiveDirectImageComplexMap f (PushforwardBicomplex.godementDirectImageTotalMap f α) =
      AdditiveImage.additiveDirectImageComplexMap f α ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map
          (Cech.additiveGodementTotalAugmentation L) :=
  (AdditiveImage.additiveDirectImageComplexMap_precompose f (PushforwardBicomplex.godementDirectImageTotalMap f α)
      (Bicomplex.godementTotalAugmentation K)).symm.trans
    ((congrArg (AdditiveImage.additiveDirectImageComplexMap f) (PushforwardBicomplex.godementDirectImageTotalMap_augmentation f α)).trans
      (AdditiveImage.additiveDirectImageComplexMap_postcompose f α (Bicomplex.godementTotalAugmentation L)))

theorem godementDirectImageTotalMap_global_quasiIso
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    (hK : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X r)))
    (hL : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := Y)
      (fun i => (Opens.map f).obj (U i)) ((Complex.SheafForget.Flasque.sheafForget Y).obj (L.X r)))
    (hα : QuasiIso (Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U (AdditiveImage.additiveDirectImageComplexMap f α))) :
    QuasiIso (Betti.Sheaf.CechPullbackTotal.topGlobalSectionsPullback f
      (AdditiveImage.additiveDirectImageComplexMap f (PushforwardBicomplex.godementDirectImageTotalMap f α))) := by
  apply Cech.Column.topGlobalSectionsPullback_quasiIso_of_coefficientSquare f U
    (AdditiveImage.additiveDirectImageComplexMap f α) _ (Cech.additiveGodementTotalAugmentation K)
    (Cech.additiveGodementTotalAugmentation L) (godementDirectImageTotalMap_additiveAugmentation f α) hU hV
  · intro q
    have := TotalFlasque.godementTotal_isFlasque K q
    exact Complex.SheafForget.Flasque.sheafForgetFlasque ((Bicomplex.godementTotal K).X q)
  · intro q
    have := TotalFlasque.godementTotal_isFlasque L q
    exact Complex.SheafForget.Flasque.sheafForgetFlasque ((Bicomplex.godementTotal L).X q)
  · exact Cech.godementCechTotalMap_quasiIso U K hK
  · exact Cech.godementCechTotalMap_quasiIso (fun i => (Opens.map f).obj (U i)) L hL
  · exact hα

end

end OAI.AlgebraicGeometry.Comparison.Betti.Godement.CechImage
