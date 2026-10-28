import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct

/-! # Witt Form Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf

noncomputable section

/-! Finite ambient-ring biproducts for the original bounded smooth Witt form presheaves. -/

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

abbrev Index (m : ℕ) := Fin (Fintype.card (Set.powersetCard σ m))

def basis (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n) (m : ℕ) :
    Module.Basis (Index σ m) ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  (WittFormBasis.basis p k A C σ ρ hρ hker hbase n U m).reindex (Fintype.equivFin (Set.powersetCard σ m))

theorem basis_natural {U V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n}
    (α : U ⟶ V) (m : ℕ) (i : Index σ m) :
    RelativeCrystalline.FormData.formsMap H Q π α m (basis p k A C σ ρ hρ hker hbase n V m i) = basis p k A C σ ρ hρ hker hbase n U m i := by
  simp only [basis, Module.Basis.reindex_apply]
  exact WittFormBasis.basis_natural p k A C σ ρ hρ hker hbase n α m
    ((Fintype.equivFin (Set.powersetCard σ m)).symm i)

def freeIso (m : ℕ) : RelativeCrystalline.FreePresheaf.presheaf H (Index σ m) ≅
    RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m :=
  RelativeCrystalline.FreePresheaf.iso H Q π (Index σ m) m
    (fun U => basis p k A C σ ρ hρ hker hbase n U m) (fun α => basis_natural p k A C σ ρ hρ hker hbase n α m)

def biproductIso (m : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m ≅
    ⨁ (fun _ : Index σ m => Crystalline.FreePresheafBiproduct.ambientPresheaf H) :=
  (freeIso p k A C σ ρ hρ hker hbase n m).symm ≪≫ Crystalline.FreePresheafBiproduct.iso H (Index σ m)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormPresheaf
