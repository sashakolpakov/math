import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSectionsIdentity

/-! # Section Map Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SectionMapQuasiIso

noncomputable section

/-! The literal balanced section map has the same quasi-isomorphism
property as its proved constant-section coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

private theorem congr_iff {D : Type*} [Category D] [HasZeroMorphisms D]
    {K L : CochainComplex D ℕ} [∀ n, K.HasHomology n] [∀ n, L.HasHomology n]
    {a b : K ⟶ L} (h : a = b) : QuasiIso a ↔ QuasiIso b := by
  cases h
  rfl

universe u z
variable {C : Type u} [Category.{0} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (g : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ⟶ I.cocomplex)

private def postMap :
    ConstantSection.ComplexMap.target.{u,0,u,z} R J
      (Sheafified.ConstantCochainCoordinates.sheafComplex R J P) ⟶
    ConstantSection.ComplexMap.target.{u,0,u,z} R J I.cocomplex :=
  ((Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex
    (.up ℕ)).map g

private def balancedMap : ConstantSection.ComplexMap.source R M ⟶
    ConstantSection.ComplexMap.target.{u,0,u,z} R J I.cocomplex :=
  SheafifiedCone.Comparison.sectionsMap.{u,z} R J I M P a g

private theorem maps_eq : balancedMap R J I M P a g =
    ConstantSection.ComplexMap.map.{u,0,u,z} R J M
      (Sheafified.ConstantCochainCoordinates.sheafComplex R J P)
      (Sheafified.ConstantCochainCoordinates.sheafMap R J M P a) ≫ postMap R J I P g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

abbrev quasiIso_iff := congr_iff (maps_eq R J I M P a g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SectionMapQuasiIso
