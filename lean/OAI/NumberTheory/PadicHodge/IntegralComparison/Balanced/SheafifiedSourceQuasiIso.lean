import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexQuasiIso

/-! # Sheafified Source Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceQuasiIso.Coordinates

noncomputable section

/-! Quasi-isomorphism in the normalized source coordinates certifies the
original balanced cone's canonical section map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u z
variable {C : Type u} [Category.{0} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  {Y : Sheaf J (ModuleCat.{u} R)} (I : InjectiveResolution Y)
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)
  (g : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ⟶ I.cocomplex)
  (M' : CochainComplex (ModuleCat.{u} R) ℕ)
  (L : CochainComplex (Sheaf J (ModuleCat.{u} R)) ℕ)
  (e : M ≅ M') (t : Sheafified.ConstantCochainCoordinates.sheafComplex R J P ≅ L)
  (b : ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M' ⟶ L)
  (h : Sheafified.ConstantCochainCoordinates.sheafMap R J M P a ≫ t.hom =
    ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map e.hom ≫ b)

abbrev quasiIso_iff := ConstantSection.ComplexQuasiIso.transported.{u,0,u,z}
  R J e g (Sheafified.ConstantCochainCoordinates.sheafMap R J M P a) t b h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.SheafifiedSourceQuasiIso.Coordinates
