import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.RelativeFormBasis

/-! # Witt Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittVanishing

noncomputable section

/-!
# IntegralComparison: bounded smooth Witt crystalline cohomology vanishes above the frame length
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.FormData

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

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Source" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p)
  (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCohomology.Comparison.complex p k A C ρ hρ hker hbase n

omit [LinearOrder σ] in
theorem form_eq_zero (U : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)) n)
    (m : ℕ) (hm : Fintype.card σ < m) (ω : RelativeCrystalline.FormData.Forms H Q π U m) : ω = 0 := by
  let e := RelativeCrystalline.Poincare.formsEquiv H Q π σ U
    (WittFrameProduct.coordinateIso p k A C σ ρ hρ hker hbase n U)
    (WittFrameProduct.coordinateIso_projection p k A C σ ρ hρ hker hbase n U) m
  exact e.injective ((Free.RelativeFormBasis.higher_form_eq_zero U.obj.ring σ U.obj.ideal
    U.obj.dividedPowers m hm (e ω)).trans e.map_zero.symm)

omit [LinearOrder σ] in
theorem presheaf_isZero (m : ℕ) (hm : Fintype.card σ < m) :
    IsZero (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m) := by
  rw [Functor.isZero_iff]
  intro U
  let : Subsingleton ((RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m).obj U) :=
    ⟨fun a b => (form_eq_zero p k A C σ ρ hρ hker hbase n U.unop m hm a).trans
      (form_eq_zero p k A C σ ρ hρ hker hbase n U.unop m hm b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

omit [LinearOrder σ] in
theorem term_isZero (m : ℕ) (hm : Fintype.card σ < m) : IsZero ((K).X m) :=
  (S).map_isZero (presheaf_isZero p k A C σ ρ hρ hker hbase n m hm)

include σ A ρ hρ hker hbase in
theorem cohomology_zero (m : ℕ) (hm : Fintype.card σ < m) :
    Subsingleton (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n m) := by
  have hterm : IsZero ((L).X m) :=
    (Ext.ModuleFunctor.functor R Source 0).map_isZero (term_isZero p k A C σ ρ hρ hker hbase n m hm)
  have hhom : IsZero ((L).homology m) := ((L).sc m).isZero_homology_of_isZero_X₂ hterm
  exact ModuleCat.subsingleton_of_isZero
    (IsZero.of_iso hhom (WittCohomology.Comparison.homologyIso p k A C σ ρ hρ hker hbase n m).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittVanishing
