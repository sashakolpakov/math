import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision

/-! # Marked Lattice Iso -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso.IntrinsicPELMarking

/-! The rational E-marking restricts to an actual integral isomorphism
from the native exponential lattice onto its marked image in E cubed. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def nativeIntegralMarking :
    HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P) ≃ₗ[ℤ] PELMarking.IntrinsicPELMarking.markedLattice A P ρ s hs hg hdegree := by
  let := NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A P ρ
  exact (RationalLattice.IntrinsicRationalPeriods.integralPeriodsEquiv (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)).trans
    (((PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree).restrictScalars ℤ).submoduleMap (RationalLattice.IntrinsicRationalPeriods.integralPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)))

theorem nativeIntegralMarking_apply (v : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A P)) :
    (nativeIntegralMarking A P ρ s hs hg hdegree v).val =
      PELMarking.IntrinsicPELMarking.coordinates A P ρ s hs hg hdegree ⟨v.val, Submodule.subset_span v.property⟩ := rfl

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso.IntrinsicPELMarking

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso

/-! A lattice-preserving E-isomorphism restricts to an actual integral
isomorphism of the two marked lattices. -/

variable {E : Type} [Field E] {V W : Type*} [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W]

def latticeLinearIso (Λ : Submodule ℤ V) (Λ' : Submodule ℤ W)
    (e : V ≃ₗ[E] W) (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ') : Λ ≃ₗ[ℤ] Λ' where
  toFun v := ⟨e v.val, (he v.val).mp v.property⟩
  invFun w := ⟨e.symm w.val, (he (e.symm w.val)).mpr
    ((congrArg (fun z => z ∈ Λ') (e.apply_symm_apply w.val)).mpr w.property)⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv w := Subtype.ext (e.apply_symm_apply w.val)
  map_add' v w := Subtype.ext (e.map_add v.val w.val)
  map_smul' a v := Subtype.ext ((e.restrictScalars ℤ).map_smul a v.val)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MarkedLatticeIso

end

end OAI
