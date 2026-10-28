import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenCombined

/-! # Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenRestriction.FrameGeometricOpenRestriction

noncomputable section

/-! The geometric frame-to-section square restricts to every open
contained in the inverse image of the target open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

private theorem restrictSquare {D : Type*} [Category* D] {A B C E F G H : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : A ⟶ F) (e : F ⟶ E)
    (r : C ⟶ G) (s : G ⟶ H) (t : E ⟶ H) (f : F ⟶ H)
    (h₁ : a ≫ b ≫ c = d ≫ e) (h₂ : r ≫ s = c ≫ t) (h₃ : e ≫ t = f) :
    a ≫ (b ≫ r) ≫ s = d ≫ f := by
  calc
    a ≫ (b ≫ r) ≫ s = (a ≫ b) ≫ (r ≫ s) := by simp only [Category.assoc]
    _ = (a ≫ b) ≫ (c ≫ t) := congrArg (fun q => (a ≫ b) ≫ q) h₂
    _ = (a ≫ b ≫ c) ≫ t := by simp only [Category.assoc]
    _ = (d ≫ e) ≫ t := congrArg (fun q => q ≫ t) h₁
    _ = d ≫ f := by rw [Category.assoc, h₃]

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated fX] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fX n FX
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fX n
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf.map g hg n FX FY a

local instance constXZero :
    (Functor.const X.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constYZero :
    (Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

theorem natural (U : Y.Opens) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ U) (i : ℕ) :
    (((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fY n).app (op FY)).f i).app (op U) ≫
      (((Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap g hg n).app ((Km).X i)).app (op U) ≫
        ((SX).obj ((T).obj ((Km).X i))).map (homOfLE h).op) ≫
          ((SX).map ((b).f i)).app (op V) =
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).map ((IntegralComparison.BoundedFrame.SectionChange.frameMap a).f i) ≫
      (((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fX n).app (op FX)).f i).app (op V) := by
  have h₁ := congrArg (fun q => (q.f i).app (op U)) (OpenCombined.FrameGeometricOpenCombined.natural g hg n a)
  have h₂ := ((SX).map ((b).f i)).naturality (homOfLE h).op
  have h₃ := (((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fX n).app (op FX)).f i).naturality (homOfLE h).op
  have h₃' : (((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fX n).app (op FX)).f i).app (op (g ⁻¹ᵁ U)) ≫
      ((SX).obj ((Kn).X i)).map (homOfLE h).op =
        (((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fX n).app (op FX)).f i).app (op V) := by
    exact h₃.symm.trans (Category.id_comp _)
  exact restrictSquare _ _ _ _ _ _ _ _ _ h₁ h₂ h₃'

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenRestriction.FrameGeometricOpenRestriction
