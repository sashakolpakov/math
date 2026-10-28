import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.FunctorMap

/-! # Intrinsic Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution.BigCrystallineIntrinsicResolution

noncomputable section

/-! # The original big-site frame resolution restricts to the native resolution -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "Big" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.functions p k B σ a
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a

def restriction : (Bigᵒᵖ ⥤ ModuleCat W) ⥤ (Cᵒᵖ ⥤ ModuleCat W) :=
  (Functor.whiskeringLeft Cᵒᵖ Bigᵒᵖ (ModuleCat W)).obj (ι).op

instance restriction_additive : (restriction p k B).Additive := by
  unfold restriction
  infer_instance

omit [Fintype σ] in
def derivative (i : σ) : F ⟶ F :=
  Functor.whiskerLeft (ι).op (FrameOperators.BigCrystallineFrameOperators.derivative (p := p) (J := I) (δ := γ) (base := bX) a i)

omit [Fintype σ] in
theorem commute (Q : Cᵒᵖ) (i j : σ) :
    Function.Commute (Koszul.Functor.KoszulFunctor.derivatives W σ F (derivative p k B σ a) Q i)
      (Koszul.Functor.KoszulFunctor.derivatives W σ F (derivative p k B σ a) Q j) :=
  FreeDivided.Derivation.FreeDividedDerivation.derivations_commute Q.unop.thickening.ring σ i j

omit [Fintype σ] in
theorem derivative_compatibility (Q : Cᵒᵖ) (i : σ) (x : (F).obj Q) :
    ((IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.iso p k B σ a).hom.app Q).hom
        (Koszul.Functor.KoszulFunctor.derivatives W σ F (derivative p k B σ a) Q i x) =
      Koszul.Functor.KoszulFunctor.derivatives W σ G (CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a) Q i
        (((IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.iso p k B σ a).hom.app Q).hom x) := by
  change DividedPowerAlgebra Q.unop.thickening.ring (σ →₀ Q.unop.thickening.ring) at x
  exact (Divided.Translations.DividedTranslations.derivative_equiv Q.unop.thickening.ring σ
    (RingHom.ker Q.unop.thickening.reduction) Q.unop.thickening.dividedPowers
    (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference p k B σ a Q.unop)
    (IntrinsicLifts.BigCrystallineIntrinsicLifts.difference_mem p k B σ a Q.unop) i x).symm

def restrictionIso : ((restriction p k B).mapHomologicalComplex (.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a) ≅
      Koszul.Functor.KoszulFunctor.complex W σ F (derivative p k B σ a) (commute p k B σ a) :=
  Iso.refl _

def iso : ((restriction p k B).mapHomologicalComplex (.up ℕ)).obj
    (FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := I) (δ := γ) (base := bX) a) ≅
      CrystallineFrame.Resolution.CrystallineFrameResolution.complex p k B σ a := by
  let f := Koszul.FunctorMap.KoszulFunctorMap.map W σ (derivative p k B σ a) (CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a)
      (commute p k B σ a) (CrystallineFrame.Resolution.CrystallineFrameResolution.commute p k B σ a)
      (IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.iso p k B σ a).hom (derivative_compatibility p k B σ a)
  let : IsIso f := Koszul.FunctorMap.KoszulFunctorMap.map_isIso W σ (derivative p k B σ a)
    (CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a) (commute p k B σ a)
    (CrystallineFrame.Resolution.CrystallineFrameResolution.commute p k B σ a)
    (IntrinsicCoordinates.BigCrystallineIntrinsicCoordinates.iso p k B σ a).hom (derivative_compatibility p k B σ a)
  let e := asIso f
  exact restrictionIso p k B σ a ≪≫ e

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicResolution.BigCrystallineIntrinsicResolution
