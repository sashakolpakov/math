import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisSheafificationInverse
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.BasisIsomorphisms

/-! # Basis Sheafification Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A compatible map from a module presheaf that is an isomorphism on a topological basis identifies its sheafification with the target sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} {ι : Type v} {B : ι → X.Opens} {P : X.PresheafOfModules} {N : X.Modules}
variable (D : PresheafModuleBasisMaps.PresheafModuleBasisMap B P N) (hB : Opens.IsBasis (Set.range B))
variable (hD : ∀ i, Function.Bijective (D.app i))

def PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationInverse : N ⟶ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P :=
  (D.inverseBasisMap hD).extend hB

theorem PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationInverse_hom : D.sheafificationInverse hB hD ≫ D.sheafificationMap hB = 𝟙 N := by
  apply Module.BasisIsomorphisms.moduleMap_eq_of_basis B hB
  intro i
  apply ConcreteCategory.hom_ext
  intro x
  have hi := (D.inverseBasisMap hD).extend_app hB i x
  exact (congrArg ((D.sheafificationMap hB).val.app (.op (B i))) hi).trans
    ((D.sheafificationMap_unit_app hB i ((D.basisEquiv hD i).symm x)).trans
      ((D.basisEquiv hD i).apply_symm_apply x))

theorem PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationHom_inverse : D.sheafificationMap hB ≫ D.sheafificationInverse hB hD = 𝟙 _ := by
  let L : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv P L).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map_injective
  apply TopCat.Sheaf.hom_ext P.presheaf ⟨L.presheaf, L.isSheaf⟩ hB
  intro i
  apply ConcreteCategory.hom_ext
  intro x
  have hf := D.sheafificationMap_unit_app hB i x
  have hi := (D.inverseBasisMap hD).extend_app hB i (D.app i x)
  have he := congrArg
    (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app (.op (B i)))
    ((D.basisEquiv hD i).symm_apply_apply x)
  exact (congrArg ((D.sheafificationInverse hB hD).val.app (.op (B i))) hf).trans (hi.trans he)

def PresheafModuleBasisMaps.PresheafModuleBasisMap.sheafificationIso : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P ≅ N where
  hom := D.sheafificationMap hB
  inv := D.sheafificationInverse hB hD
  hom_inv_id := D.sheafificationHom_inverse hB hD
  inv_hom_id := D.sheafificationInverse_hom hB hD

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
