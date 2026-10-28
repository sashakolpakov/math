import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Basis

/-! # Witt Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormBasis

noncomputable section

/-! Natural coordinate bases for the actual bounded smooth Witt relative form complex. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "xF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCoordinates.frameCoordinate p k A σ n

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

def basis (m : ℕ) : Module.Basis (Set.powersetCard σ m) ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  RelativeCrystalline.Basis.basis H Q π σ U
    (WittFrameProduct.coordinateIso p k A C σ ρ hρ hker hbase n U)
    (WittFrameProduct.coordinateIso_projection p k A C σ ρ hρ hker hbase n U) m

theorem basis_apply (m : ℕ) (s : Set.powersetCard σ m) :
    basis p k A C σ ρ hρ hker hbase n U m s = RelativeFrame.Symbols.form H Q π (F).obj τ σ xF U m s :=
  RelativeCrystalline.Basis.basis_eq_symbol H Q π σ U
    (WittFrameProduct.coordinateIso p k A C σ ρ hρ hker hbase n U)
    (WittFrameProduct.coordinateIso_projection p k A C σ ρ hρ hker hbase n U)
    (WittCoordinates.coordinate p k A C σ ρ hρ hker hbase n U)
    (fun i => ((Q).map (WittFrameProduct.presentationMorphism p k A C σ ρ hρ hker hbase n U)).ringMap (xF i))
    (WittCoordinates.coordinate_formula p k A C σ ρ hρ hker hbase n U) m s

include σ in
theorem forms_free (m : ℕ) : Module.Free ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  Module.Free.of_basis (basis p k A C σ ρ hρ hker hbase n U m)

include σ in
theorem forms_finite (m : ℕ) : Module.Finite ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  Module.Finite.of_basis (basis p k A C σ ρ hρ hker hbase n U m)

variable {U} {V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n}

theorem basis_natural (α : U ⟶ V) (m : ℕ) (s : Set.powersetCard σ m) :
    RelativeCrystalline.FormData.formsMap H Q π α m (basis p k A C σ ρ hρ hker hbase n V m s) = basis p k A C σ ρ hρ hker hbase n U m s :=
  (congrArg (RelativeCrystalline.FormData.formsMap H Q π α m) (basis_apply p k A C σ ρ hρ hker hbase n V m s)).trans
    ((RelativeFrame.Symbols.form_natural H Q π (F).obj τ σ xF α m s).trans
      (basis_apply p k A C σ ρ hρ hker hbase n U m s).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormBasis
