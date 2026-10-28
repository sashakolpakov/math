import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCechImage
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.Row

/-! # Column -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column

noncomputable section

section

/-! The actual Čech pullback total retains precomposition and postcomposition of coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex₂

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

local instance cechPullbackCompositionPushforward : (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

variable {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {L L' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ}
  (α : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj L)

theorem sheafCechPullbackBicomplexMap_postcompose (β : L ⟶ L') :
    Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U
        (α ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map β) =
      Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U α ≫
        Row.additiveSheafSectionCechBicomplexMap (fun i => (Opens.map f).obj (U i)) β := by
  apply HomologicalComplex.Hom.ext
  funext r
  exact (AdditiveCechImage.additiveCechPullback_postcompose f U (α.f r).hom (β.f r).hom).symm

theorem sheafCechPullbackBicomplexMap_precompose (β : K' ⟶ K) :
    Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U (β ≫ α) =
      Row.additiveSheafSectionCechBicomplexMap U β ≫ Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U α := by
  apply HomologicalComplex.Hom.ext
  funext r
  change (cechComplexFunctor U).map ((β.f r).hom ≫ (α.f r).hom) ≫ _ =
    (cechComplexFunctor U).map (β.f r).hom ≫ ((cechComplexFunctor U).map (α.f r).hom ≫ _)
  rw [Functor.map_comp]
  exact Category.assoc _ _ _

theorem sheafCechPullbackTotalMap_postcompose (β : L ⟶ L') :
    Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U
        (α ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map β) =
      Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U α ≫
        total.map (Row.additiveSheafSectionCechBicomplexMap (fun i => (Opens.map f).obj (U i)) β) (.up ℕ) :=
  (congrArg (fun a => total.map a (.up ℕ)) (sheafCechPullbackBicomplexMap_postcompose f U α β)).trans
    (total.map_comp _ _ _)

theorem sheafCechPullbackTotalMap_precompose (β : K' ⟶ K) :
    Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U (β ≫ α) =
      total.map (Row.additiveSheafSectionCechBicomplexMap U β) (.up ℕ) ≫ Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U α :=
  (congrArg (fun a => total.map a (.up ℕ)) (sheafCechPullbackBicomplexMap_precompose f U α β)).trans
    (total.map_comp _ _ _)

end

section

/-! A commuting coefficient square transports a Čech comparison to the actual global map of flasque complexes. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.HomologicalComplex₂

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} (U : ι → Opens X)

local instance cechFlasqueCriterionPushforward :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

variable {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {L L' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ}
  (α : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj L)
  (γ : K' ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj L')
  (e : K ⟶ K') (d : L ⟶ L')
  (h : e ≫ γ = α ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map d)

include h in
theorem sheafCechPullbackTotalMap_coefficientSquare :
    total.map (Row.additiveSheafSectionCechBicomplexMap U e) (.up ℕ) ≫
        Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U γ =
      Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U α ≫
        total.map (Row.additiveSheafSectionCechBicomplexMap (fun i => (Opens.map f).obj (U i)) d) (.up ℕ) :=
  (sheafCechPullbackTotalMap_precompose f U γ e).symm.trans
    ((congrArg (Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U) h).trans
      (sheafCechPullbackTotalMap_postcompose f U α d))

include h in
theorem sheafCechPullbackTotalMap_quasiIso_of_coefficientSquare
    (he : QuasiIso (total.map (Row.additiveSheafSectionCechBicomplexMap U e) (.up ℕ)))
    (hd : QuasiIso (total.map
      (Row.additiveSheafSectionCechBicomplexMap (fun i => (Opens.map f).obj (U i)) d) (.up ℕ)))
    (hα : QuasiIso (Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U α)) :
    QuasiIso (Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U γ) := by
  have hc : QuasiIso (total.map (Row.additiveSheafSectionCechBicomplexMap U e) (.up ℕ) ≫
      Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U γ) := by
    rw [sheafCechPullbackTotalMap_coefficientSquare f U α γ e d h]
    exact quasiIso_comp _ _ (hφ := hα) (hφ' := hd)
  exact quasiIso_of_comp_left _ _ (hφ := he) (hφφ' := hc)

include h in
theorem topGlobalSectionsPullback_quasiIso_of_coefficientSquare
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤)
    (hK' : ∀ q, TopCat.Sheaf.IsFlasque (K'.X q))
    (hL' : ∀ q, TopCat.Sheaf.IsFlasque (L'.X q))
    (he : QuasiIso (total.map (Row.additiveSheafSectionCechBicomplexMap U e) (.up ℕ)))
    (hd : QuasiIso (total.map
      (Row.additiveSheafSectionCechBicomplexMap (fun i => (Opens.map f).obj (U i)) d) (.up ℕ)))
    (hα : QuasiIso (Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U α)) :
    QuasiIso (Betti.Sheaf.CechPullbackTotal.topGlobalSectionsPullback f γ) :=
  Betti.Sheaf.CechPullbackTotal.topGlobalSectionsPullback_quasiIso_of_flasque f U γ hU hV hK' hL'
    (sheafCechPullbackTotalMap_quasiIso_of_coefficientSquare f U α γ e d h he hd hα)

end

/-! Actual Čech columns retain coefficient isomorphisms, zero objects, and commuting pullback squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
  {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}

theorem cechColumnMap_isIso (φ : K ⟶ L) (q : ℕ) [hφ : IsIso (φ.f q)] :
    IsIso ((Row.additiveSheafSectionCechBicomplexMap U φ).f q) := by
  let e : K.X q ≅ L.X q := @asIso _ _ _ _ (φ.f q) hφ
  exact ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).mapIso e).isIso_hom

theorem cechColumn_isZero (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ)
    (q : ℕ) (h : IsZero (K.X q)) : IsZero ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U K).X q) :=
  (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor U).map_isZero h

variable {Y : TopCat.{0}} (f : Y ⟶ X)

local instance cechColumnSquareAbPush : (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).Additive where
  map_add := by intros; rfl

variable {A A' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ}
  {B B' : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} Y) ℕ}
  (α : A ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj B)
  (γ : A' ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).obj B')
  (e : A ⟶ A') (d : B ⟶ B')
  (h : e ≫ γ = α ≫ ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).mapHomologicalComplex (.up ℕ)).map d)

include h in
theorem sheafCechPullbackBicomplexMap_coefficientSquare :
    Row.additiveSheafSectionCechBicomplexMap U e ≫ Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U γ =
      Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U α ≫
        Row.additiveSheafSectionCechBicomplexMap (fun i => (Opens.map f).obj (U i)) d :=
  (sheafCechPullbackBicomplexMap_precompose f U γ e).symm.trans
    ((congrArg (Betti.Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap f U) h).trans
      (sheafCechPullbackBicomplexMap_postcompose f U α d))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.Column
