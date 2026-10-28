import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses

/-! # Resolution Homology -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionHomology

noncomputable section

/-! Positive sheaf cohomology as the homology of actual global resolution sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
variable (R : InjectiveResolution F)

def sheafResolutionSections : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((Holomorphic.PeriodSequence.abelianSheafSections X ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex

def sheafResolutionCyclesClass (n : ℕ) :
    ((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).g.hom.ker →+ CategoryTheory.Sheaf.H F (n + 1) where
  toFun s := ResolutionClasses.sheafResolutionCycleClass R (n + 1) s.val s.property
  map_zero' := by
    change R.extMk ((ResolutionClasses.sheafHomGlobalEquiv _).symm 0) _ _ _ = 0
    simp only [map_zero, InjectiveResolution.extMk_zero]
  map_add' s t := by
    dsimp only [ResolutionClasses.sheafResolutionCycleClass]
    simp only [AddSubgroup.coe_add]
    rw [R.add_extMk]
    congr 1
    exact (ResolutionClasses.sheafHomGlobalEquiv (R.cocomplex.X (n + 1))).symm.map_add s.val t.val

theorem sheafResolutionCyclesClass_eq_zero_iff (n : ℕ)
    (s : ((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).g.hom.ker) :
    sheafResolutionCyclesClass R n s = 0 ↔
      s ∈ ((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).abToCycles.range := by
  rw [AddMonoidHom.mem_range]
  change ResolutionClasses.sheafResolutionCycleClass R (n + 1) s.val s.property = 0 ↔ _
  rw [ResolutionClasses.sheafResolutionCycleClass_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, congrArg Subtype.val ht⟩

def sheafResolutionQuotientClass (n : ℕ) :
    (((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).g.hom.ker ⧸
      ((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).abToCycles.range) →+
        CategoryTheory.Sheaf.H F (n + 1) :=
  QuotientAddGroup.lift _ (sheafResolutionCyclesClass R n) (by
    intro s hs
    exact (sheafResolutionCyclesClass_eq_zero_iff R n s).mpr hs)

theorem sheafResolutionQuotientClass_bijective (n : ℕ) :
    Function.Bijective (sheafResolutionQuotientClass R n) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective q
    change sheafResolutionCyclesClass R n s = 0 at hq
    exact (QuotientAddGroup.eq_zero_iff _).mpr ((sheafResolutionCyclesClass_eq_zero_iff R n s).mp hq)
  · intro a
    obtain ⟨s, hs, hsa⟩ := ResolutionClasses.exists_sheafResolutionCycle R (n + 1) a
    exact ⟨QuotientAddGroup.mk (⟨s, hs⟩ : ((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).g.hom.ker), hsa⟩

/-- This equivalence uses the existing homology quotient and the native Ext representative map. -/
def sheafResolutionHomologyEquiv (n : ℕ) :
    (sheafResolutionSections R).homology (n + 1) ≃+ CategoryTheory.Sheaf.H F (n + 1) :=
  (((ShortComplex.homologyFunctor AddCommGrpCat).mapIso
    ((sheafResolutionSections R).isoSc' n (n + 1) (n + 1 + 1)
      (CochainComplex.prev_nat_succ n)
      ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl)))).addCommGroupIsoToAddEquiv).trans
    ((((sheafResolutionSections R).sc' n (n + 1) (n + 1 + 1)).abHomologyIso.addCommGroupIsoToAddEquiv).trans
    (AddEquiv.ofBijective (sheafResolutionQuotientClass R n) (sheafResolutionQuotientClass_bijective R n)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionHomology
