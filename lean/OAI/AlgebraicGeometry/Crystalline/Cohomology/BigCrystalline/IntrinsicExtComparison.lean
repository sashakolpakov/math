import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.CoefficientComparison

/-! # Intrinsic Ext Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicExtComparison.BigCrystallineIntrinsicExtComparison

noncomputable section

/-! # Original big-to-native Ext comparison for every coefficient sheaf -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open _root_.CategoryTheory.Abelian

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X₀
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport.restriction p k B
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map.Comparison.restriction (p := p) (J := I) (δ := γ) bX
local notation "E" => OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineSheafAdapter.SmallCrystallineAdapter.modulesEquivalence (p := p) (k := k) (X := X₀)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX
local notation "Big" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.ModuleSheaf (p := p) (J := I) (δ := γ) bX

instance affineSeparated : IsSeparated (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B).hom := by
  change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  infer_instance

instance baseSeparated : IsSeparated bX := NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline.Comparison.wittSeparated p k X₀

instance restriction_preservesInjectives : (F).PreservesInjectiveObjects :=
  inferInstanceAs ((G ⋙ (E).functor).PreservesInjectiveObjects)

theorem hom_bijective (Y : Big) : Function.Bijective
    ((F).map : (A ⟶ Y) → ((F).obj A ⟶ (F).obj Y)) := by
  have hb := NumberTheory.PadicHodge.IntegralComparison.LocalConstantSheafRestriction.map_bijective
    (NumberTheory.PadicHodge.IntegralComparison.Crystalline.PresentationCover.inclusion p k X₀)
    NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site.AffineThickening.topology NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology
    (ModuleCat.{u + 1} R) (ModuleCat.of R R) Y
  have he : Function.Bijective ((E).functor.map : ((G).obj A ⟶ (G).obj Y) →
      ((E).functor.obj ((G).obj A) ⟶ (E).functor.obj ((G).obj Y))) :=
    ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  exact he.comp hb

theorem mapExt_bijective (Y : Big) (n : ℕ) : Function.Bijective ((F).mapExtAddHom A Y n) :=
  NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion.Comparison.bijective_of_hom_bijective F A (hom_bijective p k B) Y n

def equivalence (Y : Big) (n : ℕ) : Ext.{u + 2} A Y n ≃ₗ[R]
    Ext.{u + 2} ((F).obj A) ((F).obj Y) n :=
  LinearEquiv.ofBijective ((F).mapExtLinearMap R A Y n) (mapExt_bijective p k B Y n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicExtComparison.BigCrystallineIntrinsicExtComparison
