import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledIdealKernel
import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ImmersionSmoothImage

/-! # Center Incidence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Integral.CenterIncidence.Construction

noncomputable section

/-! Vanishing on a nonempty open part of an integral center forces containment in that whole center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem integral_center_kernel_of_nonempty_open
    {V Z X : Scheme.{u}} [IsIntegral Z] [Nonempty V]
    (j : V ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) : (j ≫ i).ker = i.ker := by
  let : IsDominant j := ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j)⟩
  let : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  rw [Scheme.Hom.ker_comp, j.ker_eq_bot, Scheme.IdealSheafData.map_bot]

theorem idealSheaf_contains_integral_center_of_open_vanishing
    {V Z X : Scheme.{u}} [IsIntegral Z] [Nonempty V]
    (j : V ⟶ Z) [IsOpenImmersion j] (i : Z ⟶ X) (H : X.IdealSheafData)
    (h : H.comap (j ≫ i) = ⊥) : H ≤ i.ker := by
  rw [← integral_center_kernel_of_nonempty_open j i]
  exact (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot H (j ≫ i)).mpr h

theorem idealSheaf_contains_integral_subscheme_of_open_vanishing
    {X : Scheme.{u}} (I H : X.IdealSheafData) [IsIntegral I.subscheme]
    (U : I.subscheme.Opens) [Nonempty U.toScheme]
    (h : H.comap (U.ι ≫ I.subschemeι) = ⊥) : H ≤ I := by
  have hle := idealSheaf_contains_integral_center_of_open_vanishing U.ι I.subschemeι H h
  rw [Scheme.IdealSheafData.ker_subschemeι] at hle
  exact hle

theorem integral_center_contains_of_affine_containment
    {X : Scheme.{u}} (I H : X.IdealSheafData) [IsIntegral I.subscheme]
    (U : X.affineOpens) (hproper : I.ideal U ≠ ⊤) (hH : H.ideal U ≤ I.ideal U) : H ≤ I := by
  let : Nontrivial (Γ(X, U) ⧸ I.ideal U) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let j : Spec (.of (Γ(X, U) ⧸ I.ideal U)) ⟶ I.subscheme := I.subschemeCover.f U
  let : IsOpenImmersion j := I.subschemeCover.openCover.map_prop U
  have hcomp : j ≫ I.subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec := by
    have he := I.subschemeCover_map_subschemeι U
    change j ≫ I.subschemeι =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.isoSpec.inv) ≫ U.1.ι at he
    exact he.trans (Category.assoc _ _ _)
  have hzero : H.comap (j ≫ I.subschemeι) = ⊥ := by
    rw [hcomp, Scheme.IdealSheafData.comap_comp]
    apply (ControlledIdealKernel.Construction.idealSheaf_le_ker_iff_comap_eq_bot _ _).mp
    rw [Affine.IdealSheafIdentification.Construction.idealSheaf_comap_fromSpec_eq_quotient_kernel]
    exact Global.DifferentialTransform.Construction.affineQuotientKernel_mono hH
  have hle := idealSheaf_contains_integral_center_of_open_vanishing j I.subschemeι H hzero
  rw [Scheme.IdealSheafData.ker_subschemeι] at hle
  exact hle

theorem integral_center_affine_ideal_prime
    {X : Scheme.{u}} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (U : X.affineOpens) (hproper : I.ideal U ≠ ⊤) : (I.ideal U).IsPrime := by
  let : Nontrivial (Γ(X, U) ⧸ I.ideal U) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let j : Spec (.of (Γ(X, U) ⧸ I.ideal U)) ⟶ I.subscheme := I.subschemeCover.f U
  let : IsOpenImmersion j := I.subschemeCover.openCover.map_prop U
  have hi : IsIntegral (Spec (.of (Γ(X, U) ⧸ I.ideal U))) := isIntegral_of_isOpenImmersion j
  exact (Ideal.Quotient.isDomain_iff_prime (I.ideal U)).mp
    ((affine_isIntegral_iff (.of (Γ(X, U) ⧸ I.ideal U))).mp hi)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Integral.CenterIncidence.Construction
