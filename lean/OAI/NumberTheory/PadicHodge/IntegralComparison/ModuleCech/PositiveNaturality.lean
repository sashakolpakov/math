import OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveCover

/-! # Positive Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveNaturality

noncomputable section

/-! Positive-degree change of affine cover preserves the action
and bijectivity of an actual coefficient-module map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem bijective_of_square {A B C D : AddCommGrpCat} (e : A ≅ B) (s : C ≅ D)
    (a : A ⟶ C) (b : B ⟶ D) (h : a ≫ s.hom = e.hom ≫ b)
    (ha : Function.Bijective a) : Function.Bijective b := by
  have hb : b = e.inv ≫ a ≫ s.hom := by
    apply (cancel_epi e.hom).1
    rw [Iso.hom_inv_id_assoc, h]
  rw [hb]
  exact s.addCommGroupIsoToAddEquiv.bijective.comp
    (ha.comp e.symm.addCommGroupIsoToAddEquiv.bijective)

universe u
variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) [X.left.IsSeparated]
  {ι κ : Type u} (U : ι → X.left.Opens) (V : κ → X.left.Opens)
  (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  {M N : X.left.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
  (a : M ⟶ N) (g : ℕ) (hg : 0 < g)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.CohomologyNaturality.forgetCoefficients R

theorem naturality :
    (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X U a) g) ≫
      (PositiveCover.Comparison.iso R X U V hU hV haU haV N g hg).hom =
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M g hg).hom ≫
      (G).map (HomologicalComplex.homologyMap (CohomologyNaturality.map R X V a) g) := by
  cases g with
  | zero => exact (Nat.lt_irrefl 0 hg).elim
  | succ n => exact Cover.Comparison.naturality R X U V hU hV haU haV a n

include hU hV haU haV hg in
theorem bijective
    (h : Function.Bijective (HomologicalComplex.homologyMap
      (CohomologyNaturality.map R X U a) g)) :
    Function.Bijective (HomologicalComplex.homologyMap
      (CohomologyNaturality.map R X V a) g) :=
  bijective_of_square
    (PositiveCover.Comparison.iso R X U V hU hV haU haV M g hg)
    (PositiveCover.Comparison.iso R X U V hU hV haU haV N g hg)
    _ _ (naturality R X U V hU hV haU haV a g hg) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.PositiveNaturality
