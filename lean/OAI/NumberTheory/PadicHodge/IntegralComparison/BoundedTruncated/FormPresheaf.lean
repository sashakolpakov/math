import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct

/-! # Form Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormPresheaf

noncomputable section

/-! Finite ambient-ring biproducts for the original bounded smooth finite-level form presheaves. -/

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

abbrev Index (m : ℕ) := Fin (Fintype.card (Set.powersetCard σ m))

def basis (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n) (m : ℕ) :
    Module.Basis (Index σ m) ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  (FormBasis.basis p k n A C σ ρ hρ hker hbase U m).reindex (Fintype.equivFin (Set.powersetCard σ m))

omit [Fintype k] in
theorem basis_natural {U V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n}
    (α : U ⟶ V) (m : ℕ) (i : Index σ m) :
    RelativeCrystalline.FormData.formsMap H Q π α m (basis p k n A C σ ρ hρ hker hbase V m i) = basis p k n A C σ ρ hρ hker hbase U m i := by
  simp only [basis, Module.Basis.reindex_apply]
  exact FormBasis.basis_natural p k n A C σ ρ hρ hker hbase α m
    ((Fintype.equivFin (Set.powersetCard σ m)).symm i)

def freeIso (m : ℕ) : RelativeCrystalline.FreePresheaf.presheaf H (Index σ m) ≅
    RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m :=
  RelativeCrystalline.FreePresheaf.iso H Q π (Index σ m) m
    (fun U => basis p k n A C σ ρ hρ hker hbase U m) (fun α => basis_natural p k n A C σ ρ hρ hker hbase α m)

def biproductIso (m : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m ≅
    ⨁ (fun _ : Index σ m => Crystalline.FreePresheafBiproduct.ambientPresheaf H) :=
  (freeIso p k n A C σ ρ hρ hker hbase m).symm ≪≫ Crystalline.FreePresheafBiproduct.iso H (Index σ m)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormPresheaf
