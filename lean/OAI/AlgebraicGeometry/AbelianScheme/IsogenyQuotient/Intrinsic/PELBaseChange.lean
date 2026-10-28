import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntrinsicFineTargetData
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange

/-! # PEL Base Change -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianScheme.IsogenyQuotient

/-! An actual PEL quotient records the isogeny and the full native
polarization, integral action, and ordered marking identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))}

structure Intrinsic.PELBaseChange.Construction.NativePELQuotient (A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T) (n : ℕ) where
  isogeny : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.polarized.abelian B.polarized.abelian
  etale : Etale isogeny.hom.left
  polarization : FrobeniusKernel.PolarizationComparison.Construction.polarizationPullbackHom isogeny.hom A.polarized.dual B.polarized.dual
    B.polarized.polarization = A.polarized.polarization.isogeny.hom ^ n
  action : ∀ a, isogeny.hom ≫ B.action.map a = A.action.map a ≫ isogeny.hom
  marking : ∀ (U : Over T.left)
    (c : LocallyConstant U.left (Multiplicative (Fin (2 * (3 * d)) → ZMod N))),
    (A.polarized.level.hom.app (.op U) c).val ≫ isogeny.hom =
      (B.polarized.level.hom.app (.op U) c).val

def IntrinsicFineTargetData.Construction.NativeFinePELTarget.toQuotient {A : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} {n : ℕ}
    {M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N} (f : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n M) :
    Intrinsic.PELBaseChange.Construction.NativePELQuotient A (M.universal.pullback f.target) n where
  isogeny := f.isogeny
  etale := f.etale
  polarization := f.polarization
  action := f.action
  marking := f.marking

variable [IsLocallyNoetherian T.left]
  {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T} {n : ℕ} (f : Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n)
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)

def Intrinsic.PELBaseChange.Construction.NativePELQuotient.fineTarget : IntrinsicFineTargetData.Construction.NativeFinePELTarget A n M where
  target := FinePELTarget.Construction.finePELClassifyingMap M hM B
  isogeny := FinePELTarget.Construction.finePELClassifyingIsogeny M hM B f.isogeny
  etale := by
    have : Etale f.isogeny.hom.left := f.etale
    exact FinePELTarget.Construction.finePELClassifyingIsogeny_etale M hM B f.isogeny
  polarization := (FinePELPolarization.Construction.finePELClassifyingIsogeny_polarization_pullback M hM B A.polarized.dual f.isogeny).trans
    f.polarization
  action := FinePELTarget.Construction.finePELClassifyingIsogeny_action M hM B f.isogeny A.action f.action
  marking := FinePELTarget.Construction.finePELClassifyingIsogeny_marking M hM B f.isogeny A.polarized.level f.marking
  polarization_unique ε r hr := by
    apply PolarizationAssembly.Construction.isogeny_eq_of_hom_eq
    apply Noetherian.PolarizationCancellation.Construction.noetherian_polarizationPullback_injective
      (FinePELTarget.Construction.finePELClassifyingIsogeny M hM B f.isogeny) A.polarized.dual _
    exact hr.trans ((FinePELPolarization.Construction.finePELClassifyingIsogeny_polarization_pullback M hM B A.polarized.dual f.isogeny).trans
      f.polarization).symm

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.fineTarget_kernel :
    Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (f.fineTarget M hM).isogeny.hom = Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.isogeny.hom :=
  FinePELTarget.Construction.finePELClassifyingIsogeny_kernel M hM B f.isogeny

theorem Intrinsic.PELBaseChange.Construction.NativePELQuotient.fineTarget_tate_preimage (U : Over T.left) (q : ℕ) [Fact q.Prime] :
    TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) (f.fineTarget M hM).isogeny.hom =
      TateComparison.Rational.isogenyTatePreimage (T := U) (q := q) f.isogeny.hom :=
  TateTransport.Construction.finePELClassifyingIsogeny_tate_preimage M hM B f.isogeny U q

end AlgebraicGeometry.AbelianScheme.IsogenyQuotient

namespace AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction

/-! Actual PEL quotients commute with arbitrary base change. Every
test scheme and ordered level section is retained in the marking law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction

theorem nativeFullLevelMap_baseChange
    {S T : Scheme.{0}} {g N : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (b : T ⟶ S) (p : A.scheme ⟶ B.scheme) (l : A.FullLevel N) (m : B.FullLevel N)
    (hl : ∀ (U : Over S)
      (c : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N))),
      (l.hom.app (.op U) c).val ≫ p = (m.hom.app (.op U) c).val)
    (U : Over T) (c : LocallyConstant U.left (Multiplicative (Fin (2 * g) → ZMod N))) :
    ((l.pullback b).hom.app (.op U) c).val ≫ (Over.pullback b).map p =
      ((m.pullback b).hom.app (.op U) c).val := by
  apply (B.baseChangePointsEquiv b U).injective
  exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map p b U _).trans
    ((congrArg (fun z => z ≫ p) (l.pullback_basis b U c)).trans
      ((hl ((Over.map b).obj U) c).trans (m.pullback_basis b U c).symm))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T U : Over (Spec (.of K))} {A B : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}

def NativePELQuotient.pullback (f : NativePELQuotient A B n) (b : U ⟶ T) :
    NativePELQuotient (A.pullback b) (B.pullback b) n where
  isogeny := f.isogeny.pullback b.left
  etale := MorphismProperty.overPullbackMap b.left f.isogeny.hom f.etale
  polarization := by
    let F := Over.pullback b.left
    have hp := congrArg F.map f.polarization
    have hpow : F.map (A.polarized.polarization.isogeny.hom ^ n) =
        (F.map A.polarized.polarization.isogeny.hom) ^ n := map_pow F.homMonoidHom _ n
    exact (FrobeniusKernel.DualMapBaseChange.Construction.polarizationPullbackHom_baseChange b.left f.isogeny.hom A.polarized.dual
      B.polarized.dual B.polarized.polarization).symm.trans (hp.trans hpow)
  action a := ((Over.pullback b.left).map_comp _ _).symm.trans
    ((congrArg ((Over.pullback b.left).map) (f.action a)).trans ((Over.pullback b.left).map_comp _ _))
  marking := nativeFullLevelMap_baseChange b.left f.isogeny.hom A.polarized.level B.polarized.level f.marking

end AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction

end

end OAI
