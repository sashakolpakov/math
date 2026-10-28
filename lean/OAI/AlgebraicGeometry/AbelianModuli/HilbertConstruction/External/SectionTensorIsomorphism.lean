import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionStructureParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionParameterNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineCechTensorIsomorphism

/-! # Section Tensor Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorIsomorphism

noncomputable section

/-! On affine frame opens, the canonical external section pairing is an isomorphism when the parameter sheaf has a frame. Consequently it identifies the actual finite Cech complex with the tensor complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y]
variable {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
variable (H : IsPullback a b f g) (M : X.Modules)

theorem affineFrame_externalStructureSectionTensorMap_isIso
    (V : X.Opens) (hV : IsAffineOpen V)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ Line.Bundles.structureModule V.toScheme) :
    IsIso (ModuleCat.ofHom (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M (Line.Bundles.structureModule Y) V)) := by
  let α := ModuleCat.ofHom (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M (Line.Bundles.structureModule Y) V)
  let β := ModuleCat.ofHom (Module.SectionTensorComparison.moduleSectionTensorComparisonApp (B := Affine.TensorSectionComparison.morphismGlobalAlgebra g)
    a f.appTop.hom M b.appTop.hom (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H) V)
  let s := ((SectionStructureParameter.parameterStructureSectionsEquiv g).rTensor
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op V))).toModuleIso
  let t := SectionStructureParameter.externalStructureParameterSectionsIso a b f.appTop.hom M V
  have h : α ≫ t.hom = s.hom ≫ β := SectionStructureParameter.externalSectionTensorMap_structure_comparison H M V
  have : IsIso β := AffineOpen.TensorBaseChange.affineFrame_moduleTensorComparison_isIso H M V hV eV
  have : IsIso (α ≫ t.hom) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff α t.hom).mp this

theorem affineFrame_externalSectionTensorMap_isIso
    (N : Y.Modules) (eN : N ≅ Line.Bundles.structureModule Y)
    (V : X.Opens) (hV : IsAffineOpen V)
    (eV : (Scheme.Modules.pullback V.ι).obj M ≅ Line.Bundles.structureModule V.toScheme) :
    IsIso (ModuleCat.ofHom (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V)) := by
  let α := ModuleCat.ofHom (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M N V)
  let β := ModuleCat.ofHom (SectionTensorMap.externalSectionTensorMap a b f.appTop.hom g.appTop.hom
    (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M (Line.Bundles.structureModule Y) V)
  let eA := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor g.appTop.hom).mapIso eN).app (op ⊤)
  let s := (eA.toLinearEquiv.rTensor
    ((Coefficient.ModulePresheaf.coefficientModulePresheaf f.appTop.hom M).obj (op V))).toModuleIso
  let t := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f.appTop.hom).mapIso
    ((Scheme.Modules.pushforward a).mapIso (Tensor.Bifunctor.tensorModuleMapIso
      (Iso.refl ((Scheme.Modules.pullback a).obj M)) ((Scheme.Modules.pullback b).mapIso eN)))).app (op V)
  have hs : Function.Bijective s.hom := s.toLinearEquiv.bijective
  have ht : Function.Bijective t.hom := t.toLinearEquiv.bijective
  have h : α ≫ t.hom = s.hom ≫ β := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n m
    exact (SectionParameterNaturality.externalSectionTensorMap_parameter_naturality a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm M eN.hom V n m).symm
  have hβ : IsIso β := affineFrame_externalStructureSectionTensorMap_isIso H M V hV eV
  have hb : Function.Bijective β := (ConcreteCategory.isIso_iff_bijective β).mp hβ
  apply (ConcreteCategory.isIso_iff_bijective α).mpr
  constructor
  · intro x y hxy
    apply hs.injective
    apply hb.injective
    exact (ConcreteCategory.congr_hom h x).symm.trans
      ((congrArg t.hom hxy).trans (ConcreteCategory.congr_hom h y))
  · intro y
    obtain ⟨u, hu⟩ := hb.surjective (t.hom y)
    obtain ⟨x, hx⟩ := hs.surjective u
    refine ⟨x, ht.injective ?_⟩
    exact (ConcreteCategory.congr_hom h x).trans ((congrArg β hx).trans hu)

theorem externalSectionCechTensorMap_isIso [X.IsSeparated]
    (L : Line.Bundles.LineBundle X) (N : Y.Modules) (eN : N ≅ Line.Bundles.structureModule Y)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
    (ha : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ Line.Bundles.structureModule (U i).toScheme)) :
    IsIso (SectionTensorMap.externalSectionCechTensorMap a b f.appTop.hom g.appTop.hom
      (Affine.TensorSectionComparison.cartesianGlobalCoefficient_compatibility H).symm L.sheaf N U) := by
  apply OrderedCech.TensorIsomorphism.CechTensorComparison.map_isIso
  intro q i
  let V : X.Opens := ∏ᶜ fun k => U (i.1 k)
  have hV : IsAffineOpen V := Affine.CechIntersections.affine_cechIntersection U ha q i.1
  have hle : V ≤ U (i.1 0) := leOfHom (Pi.π (fun k => U (i.1 k)) 0)
  exact affineFrame_externalSectionTensorMap_isIso H L.sheaf N eN V hV
    (L.frameRestrict hle (he (i.1 0)).some)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.SectionTensorIsomorphism
