import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.DifferentialScalarMap
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeAffineCover
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Submodule

/-! # Forms Affine Locality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality

noncomputable section

section

/-! Actual affine-test one-forms are determined by their values on the
affine opens of the target, including on nonreduced test algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

theorem oneForm_localRing_zero (ω : FormConstants.OneForms X)
    (hω : ∀ (U : X.left.Opens) (hU : IsAffineOpen U),
      ω.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) = 0)
    (R : CommAlgCat.{0} ℂ) [IsLocalRing R] (x : FormConstants.affineComplexTest R ⟶ X) : ω.val R x = 0 := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (Opens.mem_top (x.left (IsLocalRing.closedPoint R)))
  let S := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let i : FormConstants.affineComplexTest S ⟶ X := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  have : IsOpenImmersion i.left := by
    change IsOpenImmersion hU.fromSpec
    infer_instance
  have hr : Set.range x.left ⊆ Set.range i.left := by
    rintro _ ⟨p, rfl⟩
    change x.left p ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact ((IsLocalRing.specializes_closedPoint p).map x.left.continuous).mem_open U.isOpen hxU
  let l := IsOpenImmersion.lift i.left x.left hr
  have hl : l ≫ i.left = x.left := IsOpenImmersion.lift_fac _ _ _
  let z : FormConstants.affineComplexTest R ⟶ FormConstants.affineComplexTest S := Over.homMk l (by
    rw [← i.w, ← Category.assoc, hl]
    exact x.w)
  have hz : z ≫ i = x := Over.OverMorphism.ext hl
  obtain ⟨f, hf⟩ := DifferentialScalarMap.affineComplexMap_surjective S R z
  have hn := ω.property S R f i
  rw [hf, hz, hω U hU, map_zero] at hn
  exact hn.symm

theorem oneForm_eq_zero_of_affineOpens (ω : FormConstants.OneForms X)
    (hω : ∀ (U : X.left.Opens) (hU : IsAffineOpen U),
      ω.val (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU) = 0) : ω = 0 := by
  apply Subtype.ext
  funext R x
  let M : ∀ (P : Ideal R) [P.IsMaximal], Type := fun P _ => KaehlerDifferential ℂ (Localization.AtPrime P)
  let f : ∀ (P : Ideal R) [P.IsMaximal], KaehlerDifferential ℂ R →ₗ[R] M P :=
    fun P _ => KaehlerDifferential.map ℂ ℂ R (Localization.AtPrime P)
  apply Module.eq_zero_of_localization_maximal M f (ω.val R x)
  intro P _
  let S : CommAlgCat.{0} ℂ := CommAlgCat.of ℂ (Localization.AtPrime P)
  let g : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom ℂ R (Localization.AtPrime P))
  exact (DifferentialScalarMap.differentialMap_algebra R S (ω.val R x)).symm.trans
    ((ω.property R S g x).trans (oneForm_localRing_zero ω hω S (FormConstants.affineComplexMap g ≫ x)))

end

/-! Actual affine-test forms satisfy uniqueness on every open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Over Foundations.Scheme.ProjectiveSpace.complexBase}

theorem oneForm_eq_zero_of_localRings (ω : FormConstants.OneForms X)
    (hω : ∀ (R : CommAlgCat.{0} ℂ) [IsLocalRing R] (x : FormConstants.affineComplexTest R ⟶ X),
      ω.val R x = 0) : ω = 0 := by
  apply Subtype.ext
  funext R x
  let M : ∀ (P : Ideal R) [P.IsMaximal], Type := fun P _ => KaehlerDifferential ℂ (Localization.AtPrime P)
  let f : ∀ (P : Ideal R) [P.IsMaximal], KaehlerDifferential ℂ R →ₗ[R] M P :=
    fun P _ => KaehlerDifferential.map ℂ ℂ R (Localization.AtPrime P)
  apply Module.eq_zero_of_localization_maximal M f (ω.val R x)
  intro P _
  let S : CommAlgCat.{0} ℂ := CommAlgCat.of ℂ (Localization.AtPrime P)
  let g : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom ℂ R (Localization.AtPrime P))
  exact (DifferentialScalarMap.differentialMap_algebra R S (ω.val R x)).symm.trans
    ((ω.property R S g x).trans (hω S (FormConstants.affineComplexMap g ≫ x)))

theorem formsPullback_openCover_injective {I : Type*} (Y : I → Over Foundations.Scheme.ProjectiveSpace.complexBase)
    (i : ∀ j, Y j ⟶ X) (hi : ∀ j, IsOpenImmersion (i j).left)
    (hcover : ∀ p : X.left, ∃ j, p ∈ Set.range (i j).left)
    (ω η : FormConstants.OneForms X) (h : ∀ j, FormConstants.formsPullback (i j) ω = FormConstants.formsPullback (i j) η) : ω = η := by
  apply sub_eq_zero.mp
  apply oneForm_eq_zero_of_localRings (ω - η)
  intro R _ x
  obtain ⟨j, hj⟩ := hcover (x.left (IsLocalRing.closedPoint R))
  have : IsOpenImmersion (i j).left := hi j
  have hr : Set.range x.left ⊆ Set.range (i j).left := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map x.left.continuous).mem_open
      (i j).left.isOpenEmbedding.isOpen_range hj
  let l := IsOpenImmersion.lift (i j).left x.left hr
  have hl : l ≫ (i j).left = x.left := IsOpenImmersion.lift_fac _ _ _
  let z : FormConstants.affineComplexTest R ⟶ Y j := Over.homMk l (by
    rw [← (i j).w, ← Category.assoc, hl]
    exact x.w)
  have hz : z ≫ i j = x := Over.OverMorphism.ext hl
  have he := congrArg (fun a : FormConstants.OneForms (Y j) => a.val R z) (h j)
  change ω.val R (z ≫ i j) = η.val R (z ≫ i j) at he
  rw [hz] at he
  exact sub_eq_zero.mpr he

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FormsAffineLocality
