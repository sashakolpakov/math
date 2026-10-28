import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Picard Period Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient

noncomputable section

section

/-! The zero-Chern holomorphic Picard group is the actual quotient
of holomorphic first cohomology by integral periods. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicPeriodH1 :
    CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)) 1 →+
      CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 :=
  CategoryTheory.Sheaf.H.map (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence.holomorphicPeriodSheafMap E M) 1

theorem holomorphicPeriodH1_exponential
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)) 1) :
    PicardZero.holomorphicExponentialH1 E M (holomorphicPeriodH1 E M v) = 0 := by
  change (v.comp (Ext.mk₀ (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence.holomorphicExponentialSequence E M).f) (add_zero 1)).comp
    (Ext.mk₀ (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence.holomorphicExponentialSequence E M).g) (add_zero 1) = 0
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ShortComplex.zero,
    Ext.mk₀_zero, Ext.comp_zero]

theorem exists_integralH1_of_exponential_zero
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1)
    (hv : PicardZero.holomorphicExponentialH1 E M v = 0) :
    ∃ t : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)) 1, holomorphicPeriodH1 E M t = v :=
  Ext.covariant_sequence_exact₂ _ (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ShortExact.holomorphicExponentialSequence_shortExact E M) v hv

theorem holomorphicPeriodH1_range :
    (holomorphicPeriodH1 E M).range = (PicardZero.holomorphicExponentialH1 E M).ker := by
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    exact holomorphicPeriodH1_exponential E M t
  · exact exists_integralH1_of_exponential_zero E M v

instance holomorphicPeriodH1_range_normal : (holomorphicPeriodH1 E M).range.Normal := by
  rw [holomorphicPeriodH1_range]
  exact AddMonoidHom.normal_ker (PicardZero.holomorphicExponentialH1 E M)

def holomorphicPicardZeroQuotientEquiv :
    (CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 ⧸ (holomorphicPeriodH1 E M).range) ≃+
      (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting E M).ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (holomorphicPeriodH1_range E M)).trans
    ((QuotientAddGroup.quotientKerEquivRange (PicardZero.holomorphicExponentialH1 E M)).trans
      (AddEquiv.addSubgroupCongr (PicardZero.holomorphicExponentialH1_range E M)))

theorem holomorphicPicardZeroQuotientEquiv_mk
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    (holomorphicPicardZeroQuotientEquiv E M (QuotientAddGroup.mk v) : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M) =
      PicardZero.holomorphicExponentialH1 E M v := rfl

end

/-! Roots in the zero-Chern holomorphic Picard group, constructed by
dividing actual holomorphic first cohomology before exponentiation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicScalarSheafMap (c : ℂ) :
    AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M ⟶ AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom ({
      toFun := fun (g : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop)) => c • g
      map_zero' := smul_zero c
      map_add' := smul_add c } : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop) →+
        AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop))
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      ext g
      apply ContMDiffMap.ext
      intro x
      rfl }

theorem holomorphicScalarSheafMap_one : holomorphicScalarSheafMap E M 1 = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext g
  change AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop) at g
  apply ContMDiffMap.ext
  intro x
  exact one_smul ℂ (g x)

theorem holomorphicScalarSheafMap_add (c d : ℂ) :
    holomorphicScalarSheafMap E M (c + d) =
      holomorphicScalarSheafMap E M c + holomorphicScalarSheafMap E M d := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext g
  change AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop) at g
  apply ContMDiffMap.ext
  intro x
  exact add_smul c d (g x)

theorem holomorphicScalarSheafMap_comp (c d : ℂ) :
    holomorphicScalarSheafMap E M c ≫ holomorphicScalarSheafMap E M d =
      holomorphicScalarSheafMap E M (d * c) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext g
  change AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U.unop) at g
  apply ContMDiffMap.ext
  intro x
  exact (mul_smul d c (g x)).symm

def holomorphicScalarH1 (c : ℂ) :
    CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 →+
      CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 :=
  CategoryTheory.Sheaf.H.map (holomorphicScalarSheafMap E M c) 1

theorem holomorphicScalarH1_one
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    holomorphicScalarH1 E M 1 v = v := by
  unfold holomorphicScalarH1
  rw [holomorphicScalarSheafMap_one, CategoryTheory.Sheaf.H.map_id_apply]

theorem holomorphicScalarH1_add (c d : ℂ)
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    holomorphicScalarH1 E M (c + d) v =
      holomorphicScalarH1 E M c v + holomorphicScalarH1 E M d v := by
  unfold holomorphicScalarH1
  rw [holomorphicScalarSheafMap_add, CategoryTheory.Sheaf.H.map_add_apply]

theorem holomorphicScalarH1_mul (c d : ℂ)
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    holomorphicScalarH1 E M c (holomorphicScalarH1 E M d v) =
      holomorphicScalarH1 E M (c * d) v := by
  unfold holomorphicScalarH1
  rw [← CategoryTheory.Sheaf.H.map_comp_apply, holomorphicScalarSheafMap_comp]

theorem holomorphicScalarH1_natCast (n : ℕ)
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    holomorphicScalarH1 E M (n : ℂ) v = n • v := by
  induction n with
  | zero =>
    have h := holomorphicScalarH1_add E M 0 0 v
    rw [zero_add] at h
    simpa only [Nat.cast_zero, zero_nsmul] using
      (add_left_cancel (a := holomorphicScalarH1 E M 0 v) ((add_zero _).trans h)).symm
  | succ n ih =>
    rw [Nat.cast_succ, holomorphicScalarH1_add, ih, holomorphicScalarH1_one, succ_nsmul]

theorem exists_holomorphicH1_nsmul (n : ℕ) (hn : 0 < n)
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    ∃ w : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1, n • w = v := by
  refine ⟨holomorphicScalarH1 E M (n : ℂ)⁻¹ v, ?_⟩
  rw [← holomorphicScalarH1_natCast, holomorphicScalarH1_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)), holomorphicScalarH1_one]

theorem exists_zeroChern_holomorphicPicard_root (n : ℕ) (hn : 0 < n)
    (u : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M) (hu : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting E M u = 0) :
    ∃ w : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M,
      AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting E M w = 0 ∧ n • w = u := by
  obtain ⟨v, rfl⟩ := PicardZero.exists_holomorphicH1_of_connecting_zero E M u hu
  obtain ⟨v', hv'⟩ := exists_holomorphicH1_nsmul E M n hn v
  refine ⟨PicardZero.holomorphicExponentialH1 E M v', PicardZero.holomorphicExponentialH1_connecting E M v', ?_⟩
  rw [← map_nsmul, hv']

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient
