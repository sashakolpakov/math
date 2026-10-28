import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.FreePresheafBiproduct

/-! # Zero Form Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf

noncomputable section

/-!
# IntegralComparison: each actual étale zero-frame form presheaf is a finite ambient-ring biproduct
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

abbrev Index (m : ℕ) := Fin (Fintype.card (Set.powersetCard σ m))

def basis (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0) (m : ℕ) :
    Module.Basis (Index σ m) ((H).obj U).ring (RelativeCrystalline.FormData.Forms H Q π U m) :=
  (ZeroFormBasis.basis p k C σ U m).reindex (Fintype.equivFin (Set.powersetCard σ m))

theorem basis_natural {U V : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) 0}
    (α : U ⟶ V) (m : ℕ) (i : Index σ m) :
    RelativeCrystalline.FormData.formsMap H Q π α m (basis p k C σ V m i) = basis p k C σ U m i := by
  simp only [basis, Module.Basis.reindex_apply]
  exact ZeroFormBasis.basis_natural p k C σ α m
    ((Fintype.equivFin (Set.powersetCard σ m)).symm i)

def freeIso (m : ℕ) : RelativeCrystalline.FreePresheaf.presheaf H (Index σ m) ≅
    RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m :=
  RelativeCrystalline.FreePresheaf.iso H Q π (Index σ m) m
    (fun U => basis p k C σ U m) (fun α => basis_natural p k C σ α m)

def biproductIso (m : ℕ) : RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m ≅
    ⨁ (fun _ : Index σ m => Crystalline.FreePresheafBiproduct.ambientPresheaf H) :=
  (freeIso p k C σ m).symm ≪≫ Crystalline.FreePresheafBiproduct.iso H (Index σ m)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormPresheaf
