import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality

/-! # Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Cover.Comparison

noncomputable section

/-! Any two affine covers compute the same positive Zariski
cohomology of a quasicoherent module, naturally in that module. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R

def iso (M : X.left.Modules) [M.IsQuasicoherent] (n : ℕ) :
    (G).obj ((DimensionBound.complex R X M U).homology (n + 1)) ≅
      (G).obj ((DimensionBound.complex R X M V).homology (n + 1)) :=
  DimensionBound.cohomologyIso R X M U hU haU n ≪≫
    (DimensionBound.cohomologyIso R X M V hV haV n).symm

theorem naturality {M N : X.left.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (n : ℕ) :
    (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U f) (n + 1)) ≫
      (iso R X U V hU hV haU haV N n).hom =
    (iso R X U V hU hV haU haV M n).hom ≫
      (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X V f) (n + 1)) := by
  apply (cancel_mono (DimensionBound.cohomologyIso R X N V hV haV n).hom).mp
  simp only [iso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [CohomologyNaturality.naturality R X V hV haV f n]
  simp only [Iso.inv_hom_id_assoc]
  exact CohomologyNaturality.naturality R X U hU haU f n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.Cover.Comparison
