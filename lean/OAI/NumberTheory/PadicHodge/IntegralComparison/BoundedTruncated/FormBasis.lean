import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Coordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Basis

/-! # Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormBasis

noncomputable section

/-! Natural coordinate bases for the actual bounded smooth finite-level relative form complex. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n

local instance structureMap_separated : IsSeparated f :=
  FrameProduct.structureMap_separated p k C

open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "xF" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Coordinates.frameCoordinate p k n A σ

variable (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)

def basis (m : ℕ) : Module.Basis (Set.powersetCard σ m) ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  RelativeCrystalline.Basis.basis H Q π σ U
    (FrameProduct.coordinateIso p k n A C σ ρ hρ hker hbase U)
    (FrameProduct.coordinateIso_projection p k n A C σ ρ hρ hker hbase U) m

omit [Fintype k] [Fintype σ] in
theorem basis_apply (m : ℕ) (s : Set.powersetCard σ m) :
    basis p k n A C σ ρ hρ hker hbase U m s = RelativeFrame.Symbols.form H Q π (F).obj τ σ xF U m s :=
  RelativeCrystalline.Basis.basis_eq_symbol H Q π σ U
    (FrameProduct.coordinateIso p k n A C σ ρ hρ hker hbase U)
    (FrameProduct.coordinateIso_projection p k n A C σ ρ hρ hker hbase U)
    (Coordinates.coordinate p k n A C σ ρ hρ hker hbase U)
    (fun i => ((Q).map (FrameProduct.presentationMorphism p k n A C ρ hρ hker hbase U)).ringMap (xF i))
    (Coordinates.coordinate_formula p k n A C σ ρ hρ hker hbase U) m s

include σ in
omit [Fintype k] [Fintype σ] in
theorem forms_free (m : ℕ) : Module.Free ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  Module.Free.of_basis (basis p k n A C σ ρ hρ hker hbase U m)

include σ in
omit [Fintype k] in
theorem forms_finite (m : ℕ) : Module.Finite ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  Module.Finite.of_basis (basis p k n A C σ ρ hρ hker hbase U m)

variable {U} {V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n}

omit [Fintype k] [Fintype σ] in
theorem basis_natural (α : U ⟶ V) (m : ℕ) (s : Set.powersetCard σ m) :
    RelativeCrystalline.FormData.formsMap H Q π α m (basis p k n A C σ ρ hρ hker hbase V m s) = basis p k n A C σ ρ hρ hker hbase U m s :=
  (congrArg (RelativeCrystalline.FormData.formsMap H Q π α m) (basis_apply p k n A C σ ρ hρ hker hbase V m s)).trans
    ((RelativeFrame.Symbols.form_natural H Q π (F).obj τ σ xF α m s).trans
      (basis_apply p k n A C σ ρ hρ hker hbase U m s).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormBasis
