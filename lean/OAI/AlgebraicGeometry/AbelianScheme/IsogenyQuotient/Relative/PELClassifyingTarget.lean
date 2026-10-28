import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.RelativePEL
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.FineTargetUniqueness

/-! # PEL Classifying Target -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

noncomputable section

/-! Classify an independently constructed relative PEL quotient.
The target and isogeny keep its original all-test subgroup kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} {A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}
  {Q : Over T.left} {F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.polarized.abelian.scheme Q}

def Noetherian.RelativePEL.Construction.RelativePELQuotient.object (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n) :
    AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N (TotalParameters.Construction.totalParameter T Q) := h.choose

def Noetherian.RelativePEL.Construction.RelativePELQuotient.quotient (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n) :
    Intrinsic.PELBaseChange.Construction.NativePELQuotient (PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)) h.object n := h.choose_spec.choose

theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.kernel (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)
    (U : Over (TotalParameters.Construction.totalParameter T Q).left) (a : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme) :
    a ≫ h.quotient.isogeny.hom = 1 ↔ A.polarized.abelian.baseChangePointsMulEquiv Q.hom U a ∈
      F.points ((Over.map Q.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint Q U) := h.choose_spec.choose_spec U a

def Noetherian.RelativePEL.Construction.RelativePELQuotient.target (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) : TotalParameters.Construction.totalParameter T Q ⟶ M.space :=
  FinePELTarget.Construction.finePELClassifyingMap M hM h.object

def Noetherian.RelativePEL.Construction.RelativePELQuotient.targetIsogeny (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)).polarized.abelian
      (M.universal.polarized.abelian.pullback (h.target M hM).left) :=
  FinePELTarget.Construction.finePELClassifyingIsogeny M hM h.object h.quotient.isogeny

theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.targetIsogeny_kernel (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (U : Over (TotalParameters.Construction.totalParameter T Q).left) (a : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme) :
    a ≫ (h.targetIsogeny M hM).hom = 1 ↔ A.polarized.abelian.baseChangePointsMulEquiv Q.hom U a ∈
      F.points ((Over.map Q.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint Q U) := by
  let t : U ⟶ Over.mk (𝟙 (TotalParameters.Construction.totalParameter T Q).left) := Over.homMk U.hom (Category.comp_id _)
  have he := congrArg (fun H => a ∈ H.points U t)
    (FinePELTarget.Construction.finePELClassifyingIsogeny_kernel M hM h.object h.quotient.isogeny)
  exact (iff_of_eq he).trans (h.kernel U a)

theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.targetIsogeny_etale (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) : Etale (h.targetIsogeny M hM).hom.left := by
  have : Etale h.quotient.isogeny.hom.left := h.quotient.etale
  exact FinePELTarget.Construction.finePELClassifyingIsogeny_etale M hM h.object h.quotient.isogeny

theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.targetIsogeny_tate_preimage (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n)
    (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine) (U : Over (TotalParameters.Construction.totalParameter T Q).left)
    (q : ℕ) [Fact q.Prime] :
    TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) (h.targetIsogeny M hM).hom =
      TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) h.quotient.isogeny.hom :=
  TateTransport.Construction.finePELClassifyingIsogeny_tate_preimage M hM h.object h.quotient.isogeny U q

theorem Noetherian.RelativePEL.Construction.RelativePELQuotient.target_eq [IsLocallyNoetherian (TotalParameters.Construction.totalParameter T Q).left]
    (h : Noetherian.RelativePEL.Construction.RelativePELQuotient A Q F n) (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
    (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget (PELBaseChange.Construction.pelObjectPullback A (TotalParameters.Construction.totalParameterSource T Q)) n M)
    (hf : ∀ (U : Over (TotalParameters.Construction.totalParameter T Q).left) (a : U ⟶ (A.polarized.abelian.pullback Q.hom).scheme),
      a ≫ f.isogeny.hom = 1 ↔ A.polarized.abelian.baseChangePointsMulEquiv Q.hom U a ∈
        F.points ((Over.map Q.hom).obj U) (Relative.ParameterBaseChange.Construction.parameterBasePoint Q U)) : h.target M hM = f.target := by
  apply (h.quotient.fineTarget M hM).target_eq_of_sameKernel hM f
  intro U a
  exact (h.targetIsogeny_kernel M hM U a).trans (hf U a).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
