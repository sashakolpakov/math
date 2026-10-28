import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Basis

/-! # Zero Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormBasis

noncomputable section

/-!
# IntegralComparison: a natural coordinate basis for the actual étale zero-frame complex
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "xF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCoordinates.frameCoordinate p k C σ

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0)

def basis (m : ℕ) : Module.Basis (Set.powersetCard σ m) ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  RelativeCrystalline.Basis.basis H Q π σ U
    (ZeroFrameProduct.coordinateIso p k C σ U)
    (ZeroFrameProduct.coordinateIso_projection p k C σ U) m

theorem basis_apply (m : ℕ) (s : Set.powersetCard σ m) :
    basis p k C σ U m s = RelativeFrame.Symbols.form H Q π (F).obj τ σ xF U m s :=
  RelativeCrystalline.Basis.basis_eq_symbol H Q π σ U
    (ZeroFrameProduct.coordinateIso p k C σ U)
    (ZeroFrameProduct.coordinateIso_projection p k C σ U)
    (ZeroCoordinates.coordinate p k C σ U)
    (fun i => ((Q).map (ZeroFrameProduct.presentationMorphism p k C σ U)).ringMap (xF i))
    (ZeroCoordinates.coordinate_formula p k C σ U) m s

include σ in
theorem forms_free (m : ℕ) : Module.Free ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  Module.Free.of_basis (basis p k C σ U m)

include σ in
theorem forms_finite (m : ℕ) : Module.Finite ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  Module.Finite.of_basis (basis p k C σ U m)

variable {U} {V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0}

theorem basis_natural (α : U ⟶ V) (m : ℕ) (s : Set.powersetCard σ m) :
    RelativeCrystalline.FormData.formsMap H Q π α m (basis p k C σ V m s) = basis p k C σ U m s :=
  (congrArg (RelativeCrystalline.FormData.formsMap H Q π α m) (basis_apply p k C σ V m s)).trans
    ((RelativeFrame.Symbols.form_natural H Q π (F).obj τ σ xF α m s).trans
      (basis_apply p k C σ U m s).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormBasis
