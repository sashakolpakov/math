import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueInjectives
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Bounded Flasque Sections -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BoundedFlasqueSections.Constructions

noncomputable section

/-! Actual bounded-below exact flasque complexes remain exact after taking open sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

section StrictSupport

variable {C : Type*} [Category C] [Abelian C]
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]
variable [K.IsStrictlySupported e]

theorem strictSupportRestriction_hasLift : e.HasLift (𝟙 (K.restriction e)) := by
  intro j hj i' hi'
  exact (K.isZero_X_of_isStrictlySupported e i' (hj.notMem hi')).eq_zero_of_src _

def strictSupportRestrictionExtendMap : K ⟶ (K.restriction e).extend e :=
  e.liftExtend (𝟙 (K.restriction e)) (strictSupportRestriction_hasLift K e)

theorem strictSupportRestrictionExtendMap_isIso : IsIso (strictSupportRestrictionExtendMap K e) := by
  have : ∀ i', IsIso ((strictSupportRestrictionExtendMap K e).f i') := by
    intro i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i,hi⟩ := hi'
      apply (e.isIso_liftExtend_f_iff (𝟙 (K.restriction e))
        (strictSupportRestriction_hasLift K e) hi).mpr
      infer_instance
    · exact (K.isZero_X_of_isStrictlySupported e i' (by simpa using hi')).isIso
        ((K.restriction e).isZero_extend_X e i' (by simpa using hi')) _
  exact HomologicalComplex.Hom.isIso_of_components _

def strictSupportRestrictionExtendIso : K ≅ (K.restriction e).extend e := by
  have := strictSupportRestrictionExtendMap_isIso K e
  exact asIso (strictSupportRestrictionExtendMap K e)

theorem strictSupportRestriction_acyclic_iff : K.Acyclic ↔ (K.restriction e).Acyclic := by
  constructor
  · intro h i
    apply ((K.restriction e).extend_exactAt_iff e (j := i) (j' := e.f i) rfl).mp
    exact (h (e.f i)).of_iso (strictSupportRestrictionExtendIso K e)
  · intro h i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i,hi⟩ := hi'
      have he := ((K.restriction e).extend_exactAt_iff e hi).mpr (h i)
      exact he.of_iso (strictSupportRestrictionExtendIso K e).symm
    · exact HomologicalComplex.ExactAt.of_isZero
        (K.isZero_X_of_isStrictlySupported e i' (by simpa using hi'))

end StrictSupport

theorem rationalBoundedFlasqueSections_acyclic {X : TopCat.{0}}
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℤ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (b : ℤ) [K.IsStrictlyGE b]
    (he : K.Acyclic) (U : Opens X) :
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  let e := ComplexShape.embeddingUpIntGE b
  apply (strictSupportRestriction_acyclic_iff _ e).mpr
  have hR := (strictSupportRestriction_acyclic_iff K e).mp he
  exact FlasqueInjectives.Constructions.rationalFlasqueSections_acyclic (K.restriction e) (fun n => hK (e.f n)) hR U

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.BoundedFlasqueSections.Constructions
