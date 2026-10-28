import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.KernelSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionDifference
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Section Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SectionLocalization

noncomputable section

/-! A sheaf map that localizes sections on a finite cover and its pairwise overlaps also localizes global sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
    {F G : TopCat.Presheaf (ModuleCat.{u} R) X}
    {ι : Type v} (U : ι → Opens X) (α : F ⟶ G)

def openSectionZeroMap : ((i : ι) → F.obj (op (U i))) →ₗ[R]
    ((i : ι) → G.obj (op (U i))) :=
  LinearMap.pi fun i ↦ (α.app (op (U i))).hom.comp (LinearMap.proj i)

def openSectionOneMap : ((i j : ι) → F.obj (op (U i ⊓ U j))) →ₗ[R]
    ((i j : ι) → G.obj (op (U i ⊓ U j))) :=
  LinearMap.pi fun i ↦ (LinearMap.pi fun j ↦
    (α.app (op (U i ⊓ U j))).hom.comp (LinearMap.proj j)).comp (LinearMap.proj i)

theorem openSectionMap_square :
    (Open.SectionDifference.openSectionDifference G U).comp (openSectionZeroMap U α) =
      (openSectionOneMap U α).comp (Open.SectionDifference.openSectionDifference F U) := by
  ext x i j
  change G.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (α.app (op (U i)) (x i)) -
    G.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (α.app (op (U j)) (x j)) =
    α.app (op (U i ⊓ U j))
      (F.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (x i) -
        F.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (x j))
  rw [map_sub]
  congr 1
  · exact (ConcreteCategory.congr_hom
      (α.naturality (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op) (x i)).symm
  · exact (ConcreteCategory.congr_hom
      (α.naturality (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op) (x j)).symm

theorem sheafSections_isLocalized_of_finite_cover [Finite ι]
    (hF : F.IsSheaf) (hG : G.IsSheaf) (S : Submonoid R) (hU : iSup U = ⊤)
    (h₀ : ∀ i, IsLocalizedModule S (α.app (op (U i))).hom)
    (h₁ : ∀ i j, IsLocalizedModule S (α.app (op (U i ⊓ U j))).hom) :
    IsLocalizedModule S (α.app (op ⊤)).hom := by
  let (i : ι) := h₀ i
  let (i j : ι) := h₁ i j
  have : IsLocalizedModule S (openSectionZeroMap U α) := IsLocalizedModule.pi S _
  have : IsLocalizedModule S (openSectionOneMap U α) := by
    let (i : ι) : IsLocalizedModule S
        (LinearMap.pi fun j ↦ (α.app (op (U i ⊓ U j))).hom.comp (LinearMap.proj j)) :=
      IsLocalizedModule.pi S _
    exact IsLocalizedModule.pi S _
  let k := Localized.KernelSquare.kernelSquareMap (openSectionZeroMap U α) (openSectionOneMap U α)
    (Open.SectionDifference.openSectionDifference F U) (Open.SectionDifference.openSectionDifference G U) (openSectionMap_square U α)
  have : IsLocalizedModule S k := Localized.KernelSquare.kernelSquareMap_isLocalized S _ _ _ _ _
  let eF := Open.SectionDifference.globalOpenSectionKernelEquiv F U hF hU
  let eG := Open.SectionDifference.globalOpenSectionKernelEquiv G U hG hU
  have : IsLocalizedModule S (k.comp eF.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S k eF
  have ht := IsLocalizedModule.of_linearEquiv S (k.comp eF.toLinearMap) eG.symm
  convert ht using 1
  apply LinearMap.ext
  intro x
  apply eG.injective
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, eG.apply_symm_apply]
  apply Subtype.ext
  funext i
  exact (ConcreteCategory.congr_hom (α.naturality (U i).leTop.op) x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SectionLocalization
