import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedKernelSquare
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechDegreeZero
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! # Sheaf Sections Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafSectionsLocalization

noncomputable section

/-! Localization of sections can be checked on a finite open cover and
its pairwise intersections. The proof uses actual sheaf gluing. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech
universe u v w

variable {R : Type u} [CommRing R] {X : TopCat.{v}}
    {F G : TopCat.Sheaf (ModuleCat.{v} R) X}
    {ι : Type w} (U : ι → Opens X)

def sheafSectionsCechKernelEquiv (F : TopCat.Sheaf (ModuleCat.{v} R) X)
    (hU : iSup U = ⊤) :
    F.obj.obj (op ⊤) ≃ₗ[R] (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F U).ker :=
  LinearEquiv.ofBijective
    ((Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechUnit F U).codRestrict _ (fun s =>
      (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCech_exact_degreeZero F U hU _).mpr ⟨s, rfl⟩))
    ⟨fun x y h => Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechUnit_injective F U hU (congrArg Subtype.val h), by
      intro x
      obtain ⟨s, hs, _⟩ := Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCech_sections_glue F U hU x.val x.property
      exact ⟨s, Subtype.ext hs⟩⟩

variable (α : F ⟶ G)

def sheafCechZeroMap : Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 F U →ₗ[R] Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechC0 G U :=
  .pi fun i => (α.hom.app (op (U i))).hom.comp (.proj i)

def sheafCechOneMap : Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 F U →ₗ[R] Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechC1 G U :=
  .pi fun i => (LinearMap.pi fun j =>
    (α.hom.app (op (U i ⊓ U j))).hom.comp (.proj j)).comp (.proj i)

theorem sheafCechMap_square :
    (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 G U).comp (sheafCechZeroMap U α) =
      (sheafCechOneMap U α).comp (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F U) := by
  ext x i j
  change G.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op
      (α.hom.app (op (U j)) (x j)) -
    G.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op
      (α.hom.app (op (U i)) (x i)) =
    α.hom.app (op (U i ⊓ U j))
      (F.obj.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (x j) -
        F.obj.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (x i))
  rw [map_sub]
  congr 1
  · exact (ConcreteCategory.congr_hom
      (α.hom.naturality (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op) (x j)).symm
  · exact (ConcreteCategory.congr_hom
      (α.hom.naturality (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op) (x i)).symm

theorem sheafSections_isLocalized_of_finite_cover [Finite ι]
    (S : Submonoid R) (hU : iSup U = ⊤)
    (h₀ : ∀ i, IsLocalizedModule S (α.hom.app (op (U i))).hom)
    (h₁ : ∀ i j, IsLocalizedModule S (α.hom.app (op (U i ⊓ U j))).hom) :
    IsLocalizedModule S (α.hom.app (op ⊤)).hom := by
  let (i : ι) := h₀ i
  let (i j : ι) := h₁ i j
  have : IsLocalizedModule S (sheafCechZeroMap U α) := IsLocalizedModule.pi S _
  have : IsLocalizedModule S (sheafCechOneMap U α) := by
    let (i : ι) : IsLocalizedModule S
        (.pi fun j => (α.hom.app (op (U i ⊓ U j))).hom.comp (.proj j)) :=
      IsLocalizedModule.pi S _
    exact IsLocalizedModule.pi S _
  let k := LocalizedKernelSquare.kernelSquareMap (sheafCechZeroMap U α) (sheafCechOneMap U α)
    (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 F U) (Quotients.FiniteDescent.OpenCechDegreeZero.Construction.CubeCech.openModuleCechD0 G U) (sheafCechMap_square U α)
  have : IsLocalizedModule S k := LocalizedKernelSquare.kernelSquareMap_isLocalized S _ _ _ _ _
  let eF := sheafSectionsCechKernelEquiv U F hU
  let eG := sheafSectionsCechKernelEquiv U G hU
  have : IsLocalizedModule S (k.comp eF.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S k eF
  have ht := IsLocalizedModule.of_linearEquiv S (k.comp eF.toLinearMap) eG.symm
  convert ht using 1
  ext x
  apply eG.injective
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, eG.apply_symm_apply]
  apply Subtype.ext
  funext i
  exact (ConcreteCategory.congr_hom (α.hom.naturality (U i).leTop.op) x).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafSectionsLocalization
