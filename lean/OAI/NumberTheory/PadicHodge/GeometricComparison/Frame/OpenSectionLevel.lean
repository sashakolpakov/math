import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalOpenSectionLevel

/-! # Open Section Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionLevel.FrameOpenSectionLevel

noncomputable section

/-! The original frame-to-open-section maps commute with bounded-level
restriction and the actual frame morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

private theorem composeSquares {D : Type*} [Category* D] {A B C E F G H K : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ K)
    (e : B ⟶ F) (f : F ⟶ E) (g : F ⟶ G) (i : G ⟶ K) (l : A ⟶ H) (j : H ⟶ G)
    (h₁ : b ≫ c = e ≫ f) (h₂ : f ≫ d = g ≫ i) (h₃ : a ≫ e ≫ g = l ≫ j) :
    (a ≫ b) ≫ (c ≫ d) = l ≫ (j ≫ i) := by
  have h : b ≫ c ≫ d = (e ≫ g) ≫ i := by
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q) h).trans
      ((Category.assoc a (e ≫ g) i).symm.trans
        ((congrArg (fun q => q ≫ i) h₃).trans (Category.assoc _ _ _))))

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)
  {Fn : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {Fm : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m}
  (a : (IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj Fn ⟶ Fm)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n Fn
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f m Fm
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap.map f n m hnm a
local notation "Sn" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) f n

local instance constPreservesZero :
    (Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

theorem natural : (OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation f m).app (op Fm) ≫
    ((Bounded.OpenSectionLevel.BoundedOpenSectionLevel.transformation f n m hnm).mapHomologicalComplex (.up ℕ)).app Km ≫
      ((Sn).mapHomologicalComplex (.up ℕ)).map b =
    ((Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ)).map
      (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.SectionChange.frameMap a)) ≫
          (OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation f n).app (op Fn) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  have hL := congrArg (fun q => (q.app ((Km).X i)).app V)
    (Bounded.GlobalOpenSectionLevel.BoundedGlobalOpenSectionLevel.natural f n m hnm)
  have hN := congrArg (fun q => q.app V)
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation f n).naturality ((b).f i))
  have hG := congrArg (fun q => q.f i) (GlobalSectionLevel.FrameGlobalSectionLevel.natural f n m hnm a)
  change (((OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f m).app (op Fm)).f i ≫
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation f m).app ((Km).X i)).app V) ≫
      (((Bounded.OpenSectionLevel.BoundedOpenSectionLevel.transformation f n m hnm).app ((Km).X i)).app V ≫
        ((Sn).map ((b).f i)).app V) =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).map ((IntegralComparison.BoundedFrame.SectionChange.frameMap a).f i)) ≫
      (((OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f n).app (op Fn)).f i ≫
        ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation f n).app ((Kn).X i)).app V)
  exact composeSquares _ _ _ _ _ _ _ _ _ _ hL hN.symm hG

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionLevel.FrameOpenSectionLevel
