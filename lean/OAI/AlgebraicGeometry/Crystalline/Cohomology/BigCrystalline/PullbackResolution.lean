import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.FunctorMap

/-! # Pullback Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution

noncomputable section

/-! # The original big frame resolution under geometric affine pullback -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A B σ : Type u) [CommRing W] [CommRing A] [CommRing B]
  (J : Ideal W) (δ : DividedPowers J) (base : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of W))
  (φ : B →+* A) (a : σ → B) [Fintype σ]

local notation "bA" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ bA
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B J δ base
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A B J δ base φ
def functions : Cᵒᵖ ⥤ ModuleCat W := (ι).op ⋙ FrameFunctor.BigCrystallineFrameFunctor.functions a

local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution.functions p W A B σ J δ base φ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameFunctor.BigCrystallineFrameFunctor.functions (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameOperators.BigCrystallineFrameOperators.derivative (p := p) (J := J) (δ := δ) (base := bA) (φ ∘ a)

def restriction : (Tᵒᵖ ⥤ ModuleCat W) ⥤ (Cᵒᵖ ⥤ ModuleCat W) :=
  (Functor.whiskeringLeft Cᵒᵖ Tᵒᵖ (ModuleCat W)).obj (ι).op

instance restriction_additive : (restriction p W A B J δ base φ).Additive := by
  unfold restriction
  infer_instance

def derivative (i : σ) : F ⟶ F :=
  Functor.whiskerLeft (ι).op (FrameOperators.BigCrystallineFrameOperators.derivative
    (p := p) (J := J) (δ := δ) (base := base) a i)

omit [Fintype σ] in
theorem commute (Q : Cᵒᵖ) (i j : σ) :
    Function.Commute (Koszul.Functor.KoszulFunctor.derivatives W σ F (derivative p W A B σ J δ base φ a) Q i)
      (Koszul.Functor.KoszulFunctor.derivatives W σ F (derivative p W A B σ J δ base φ a) Q j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute Q.unop.ring σ i j

omit [Fintype σ] in
theorem derivative_compatibility (Q : Cᵒᵖ) (i : σ) (x : (F).obj Q) :
    ((PullbackCoordinates.BigCrystallinePullbackCoordinates.functionsIso p W A B σ J δ base φ a).hom.app Q).hom
      (Koszul.Functor.KoszulFunctor.derivatives W σ F (derivative p W A B σ J δ base φ a) Q i x) =
    Koszul.Functor.KoszulFunctor.derivatives W σ G E Q i
      (((PullbackCoordinates.BigCrystallinePullbackCoordinates.functionsIso p W A B σ J δ base φ a).hom.app Q).hom x) := rfl

def restrictionIso : ((restriction p W A B J δ base φ).mapHomologicalComplex (.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a) ≅
      Koszul.Functor.KoszulFunctor.complex W σ F (derivative p W A B σ J δ base φ a) (commute p W A B σ J δ base φ a) :=
  Iso.refl _

def iso : ((restriction p W A B J δ base φ).mapHomologicalComplex (.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a) ≅
      FrameResolution.BigCrystallineFrameResolution.complex (φ ∘ a) := by
  let e₀ : F ≅ G := PullbackCoordinates.BigCrystallinePullbackCoordinates.functionsIso p W A B σ J δ base φ a
  let f := Koszul.FunctorMap.KoszulFunctorMap.map W σ (derivative p W A B σ J δ base φ a) E
    (commute p W A B σ J δ base φ a) (FrameResolution.BigCrystallineFrameResolution.commute (φ ∘ a))
    e₀.hom
    (derivative_compatibility p W A B σ J δ base φ a)
  let : IsIso f := Koszul.FunctorMap.KoszulFunctorMap.map_isIso W σ (derivative p W A B σ J δ base φ a) E
    (commute p W A B σ J δ base φ a) (FrameResolution.BigCrystallineFrameResolution.commute (φ ∘ a))
    e₀.hom
    (derivative_compatibility p W A B σ J δ base φ a)
  let e := asIso f
  exact restrictionIso p W A B σ J δ base φ a ≪≫ e

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackResolution.BigCrystallinePullbackResolution
