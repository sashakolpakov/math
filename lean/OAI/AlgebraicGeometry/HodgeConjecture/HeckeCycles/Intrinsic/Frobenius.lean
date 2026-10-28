import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange

/-! # Frobenius -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM

noncomputable section

/-! The actual prime-field Albanese, its faithful geometric action,
and its q-power Frobenius on the very group used for ordinary detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j) (a : M.Family)

def residueExtension : ZMod q →+* Detection.CM.residueClosure (q := q) :=
  algebraMap (ZMod q) (Detection.CM.residueClosure (q := q))

abbrev residueExtensionBase : Spec (.of (Detection.CM.residueClosure (q := q))) ⟶ Spec (.of (ZMod q)) :=
  Spec.map (CommRingCat.ofHom (residueExtension (q := q)))

theorem geometricBase_factor :
    residueExtensionBase (q := q) ≫ R.specialBase = R.geometricBase := by
  change Spec.map (CommRingCat.ofHom (residueExtension (q := q))) ≫
    Spec.map (CommRingCat.ofHom R.residue) =
      Spec.map (CommRingCat.ofHom ((algebraMap (ZMod q) (Detection.CM.residueClosure (q := q))).comp R.residue))
  rw [← Spec.map_comp]
  rfl

def specialAlbanese : CommGrp (Over (Spec (.of (ZMod q)))) :=
  GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct (M.components a).A) R.specialBase

def geometricAssociativity :
    (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct (M.components a).A) R.geometricBase).toGrp ≅
      (GroupBaseChange.CM.changedGroup (specialAlbanese R a) (residueExtensionBase (q := q))).toGrp :=
  GroupBaseChange.CM.factorGroupIso (AbelianScheme.TateComparison.Products.componentProduct (M.components a).A)
    (residueExtensionBase (q := q)) R.specialBase R.geometricBase (geometricBase_factor R)

def geometricProductIdentification :
    (GroupBaseChange.CM.changedGroup (AbelianScheme.TateComparison.Products.componentProduct (M.components a).A) R.geometricBase).toGrp ≅
      (Detection.CM.geometricAlbanese R a).toGrp :=
  ProductBaseChange.CM.productBaseChangeGroupIso (M.components a).A R.geometricBase

def geometricIdentificationGroup :
    (GroupBaseChange.CM.changedGroup (specialAlbanese R a) (residueExtensionBase (q := q))).toGrp ≅
      (Detection.CM.geometricAlbanese R a).toGrp :=
  (geometricAssociativity R a).symm ≪≫ geometricProductIdentification R a

def geometricIdentification :
    (GroupBaseChange.CM.changedGroup (specialAlbanese R a) (residueExtensionBase (q := q))).X ≅
      (Detection.CM.geometricAlbanese R a).X :=
  (Grp.forget _).mapIso (geometricIdentificationGroup R a)

theorem geometricIdentification_group : IsMonHom (geometricIdentification R a).hom :=
  (geometricIdentificationGroup R a).hom.hom.isMonHom_hom

def specialEndEmbedding :
    {ρ : AbelianScheme.TateComparison.End.IntegralEnd (specialAlbanese R a).X →+* AbelianScheme.TateComparison.End.IntegralEnd (Detection.CM.geometricAlbanese R a).X //
      Function.Injective ρ} :=
  Finite.FieldFrobenius.CM.GroupEndAction.embedding (specialAlbanese R a) (residueExtension (q := q))
    (Detection.CM.geometricAlbanese R a) (geometricIdentificationGroup R a)

def specialEndToGeometric :
    AbelianScheme.TateComparison.End.IntegralEnd (specialAlbanese R a).X →+* AbelianScheme.TateComparison.End.IntegralEnd (Detection.CM.geometricAlbanese R a).X :=
  (specialEndEmbedding R a).val

theorem specialEndToGeometric_injective : Function.Injective (specialEndToGeometric R a) :=
  (specialEndEmbedding R a).property

def nativeFrobenius : AbelianScheme.TateComparison.End.IntegralEnd (Detection.CM.geometricAlbanese R a).X :=
  specialEndToGeometric R a (Finite.FieldFrobenius.CM.integralFrobenius (specialAlbanese R a))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM
