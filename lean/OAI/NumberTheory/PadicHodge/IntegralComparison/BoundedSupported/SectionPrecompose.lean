import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.SectionFamilyCoordinates

/-! # Section Precompose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.SectionPrecompose

noncomputable section

/-! Precomposition with the canonical change of an equal open family
agrees with the same coefficient transport in the supported complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C]
  (F G : C →o Y.Opens) (h : F = G)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

variable (L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a : L ⟶ ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ)
    fY n G).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)

abbrev comparison :=
  congrArg (fun z => a ≫ z)
    (SectionFamilyCoordinates.Family.inv fY n I F G h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.SectionPrecompose
