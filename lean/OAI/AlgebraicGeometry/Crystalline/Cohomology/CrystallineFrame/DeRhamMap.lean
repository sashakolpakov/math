import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryPolynomialEq

/-! # De Rham Map -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.DeRhamMap.CrystallineFrameDeRhamMap

noncomputable section

/-!
# Ordinary frame de Rham forms in the native crystalline resolution

The fixed polynomial frame maps naturally into the ambient functions of
every crystalline frame extension. Polynomial differentiation agrees with
the coordinate differential. Its actual ordinary de Rham complex therefore
maps naturally into the frame resolution, before and after sheafification.
-/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "P" => MvPolynomial σ W
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.functions p k B σ a
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Operators.CrystallineFrameOperators.derivative p k B σ a
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.Functor.KoszulFunctor.functor W σ F D (OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution.CrystallineFrameResolution.commute p k B σ a)

def coordinateMap (Q : Cᵒᵖ) : Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ ⟶ (K).obj Q :=
  Koszul.TensorMap.KoszulTensorMap.map W σ P ((F).obj Q) (fun i => (MvPolynomial.pderiv i).toLinearMap)
    (Koszul.Functor.KoszulFunctor.derivatives W σ F D Q) (CrystallineFrame.Functor.CrystallineFrameFunctor.polynomialMap a Q.unop).toLinearMap
    (fun i t => (Polynomial.FrameDifferential.PolynomialFrameDifferential.derivative_polynomialMap W Q.unop.thickening.ring σ
      (Lifts.CrystallineFrameLifts.lift p k B σ a Q.unop) i t).symm)
    (Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomial_derivatives_commute W σ)
    (Resolution.CrystallineFrameResolution.commute p k B σ a Q)

def coordinateTransformation :
    (Functor.const Cᵒᵖ).obj (Polynomial.FrameDifferential.PolynomialFrameDifferential.polynomialComplex W σ) ⟶ K where
  app := coordinateMap p k B σ a
  naturality {Q T} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro ω
    change CrystallineFrame.Functor.CrystallineFrameFunctor.polynomialMap a T.unop t ⊗ₜ[W] ω =
      Map.CrystallineFrameMap.ambientMap a f.unop (CrystallineFrame.Functor.CrystallineFrameFunctor.polynomialMap a Q.unop t) ⊗ₜ[W] ω
    exact congrArg (fun z => z ⊗ₜ[W] ω)
      (DFunLike.congr_fun (CrystallineFrame.Functor.CrystallineFrameFunctor.polynomialMap_naturality a f.unop) t).symm

/-- The source is the actual ordinary polynomial de Rham complex. -/
def ordinaryTransformation :
    (Functor.const Cᵒᵖ).obj (DeRhamPresentationTo.DeRhamPresentation.complex W P) ⟶ K :=
  (Functor.const Cᵒᵖ).map (OrdinaryPolynomialEq.OrdinaryPolynomialCoordinates.complexIso W σ).inv ≫
    coordinateTransformation p k B σ a

def polynomialForms : CochainComplex (Cᵒᵖ ⥤ ModuleCat W) ℕ :=
  ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.up ℕ)
    ((Functor.const Cᵒᵖ).obj (DeRhamPresentationTo.DeRhamPresentation.complex W P))

def map : polynomialForms p k B σ ⟶ Resolution.CrystallineFrameResolution.complex p k B σ a :=
  ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.up ℕ) (ordinaryTransformation p k B σ a)

def sheafPolynomialForms :=
  ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (polynomialForms p k B σ)

def sheafMap : sheafPolynomialForms p k B σ ⟶ SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a :=
  ((PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (CrystallineFrameDeRhamMap.map p k B σ a)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.DeRhamMap.CrystallineFrameDeRhamMap
