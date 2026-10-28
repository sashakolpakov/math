import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitnessConstruction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescribedKernelBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ClassifyingDataIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientWitness

/-! # Quotient Witness Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

/-! Base change transports every component of an actual PEL quotient
witness. In particular, the multiplier identity uses the canonical
dual-map comparison and the full marking is retained on all tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

universe u

def QuotientWitnessBaseChange.Construction.baseChangedKernelGroup {S T : Scheme.{u}} (f : T ⟶ S) (H : Grp (Over S)) :
    Grp (Over T) := by
  let : GrpObj ((Over.pullback f).obj H.X) := Functor.grpObjObj
  exact Grp.mk ((Over.pullback f).obj H.X)

theorem QuotientWitnessBaseChange.Construction.fullLevelMap_baseChange {S T : Scheme.{u}} {g N : ℕ}
    {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (f : T ⟶ S) (p : A.scheme ⟶ B.scheme)
    (level : A.FullLevel N) (level' : B.FullLevel N)
    (hlevel : ∀ (U : (Over S)ᵒᵖ)
      (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S).obj U),
      (level'.hom.app U c).val = (level.hom.app U c).val ≫ p)
    (U : Over T) (c : (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T).obj (op U)) :
    ((level'.pullback f).hom.app (op U) c).val =
      ((level.pullback f).hom.app (op U) c).val ≫ (Over.pullback f).map p := by
  apply (B.baseChangePointsEquiv f U).injective
  exact (level'.pullback_basis f U c).trans
    ((hlevel (op ((Over.map f).obj U)) c).trans
      ((congrArg (fun z => z ≫ p) (level.pullback_basis f U c).symm).trans
        (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map p f U _).symm))

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable {D : Integral.Construction.SplitPELReduction P iota κ M U B q}
variable {source : D.GeometricPELDatum} {m : ℕ}
variable {H : Grp (Over D.integralGeometricBase.left)}
variable {i : H.X ⟶ source.data.polarized.abelian.scheme}

/-- This operation takes an already constructed quotient witness; its
polarization and Lie conditions are transported by genuine PEL base change. -/
def Integral.Construction.SplitPELReduction.QuotientWitness.pullback (Q : D.QuotientWitness source m H i)
    (f : D.integralGeometricBase ⟶ D.integralGeometricBase) :
    D.QuotientWitness (source.pullback f) m (QuotientWitnessBaseChange.Construction.baseChangedKernelGroup f.left H)
      ((Over.pullback f.left).map i) where
  target := Q.target.pullback f
  isogeny := Q.isogeny.pullback f.left
  kernel := PrescribedKernelBaseChange.Construction.prescribedKernel_baseChange f.left Q.isogeny.hom i Q.kernel
  polarization := by
    let F := Over.pullback f.left
    let : GrpObj (F.obj source.data.polarized.dual.abelian.scheme) := Functor.grpObjObj
    have hp := congrArg (fun a => F.map a) Q.polarization
    have hpow : F.map (source.data.polarized.polarization.isogeny.hom ^ m) =
        (F.map source.data.polarized.polarization.isogeny.hom) ^ m :=
      map_pow F.homMonoidHom _ m
    exact (DualMapBaseChange.Construction.polarizationPullbackHom_baseChange f.left Q.isogeny.hom source.data.polarized.dual
      Q.target.data.polarized.dual Q.target.data.polarized.polarization).symm.trans (hp.trans hpow)
  action a := ((Over.pullback f.left).map_comp _ _).symm.trans
    ((congrArg (fun r => (Over.pullback f.left).map r) (Q.action a)).trans
      ((Over.pullback f.left).map_comp _ _))
  marking T c := QuotientWitnessBaseChange.Construction.fullLevelMap_baseChange f.left Q.isogeny.hom source.data.polarized.level
    Q.target.data.polarized.level Q.marking T.unop c

/-- The target of the actual Frobenius-base-changed quotient
classifies the independently defined Frobenius moduli point. -/
theorem Integral.Construction.SplitPELReduction.QuotientWitness.frobenius_classifies (Q : D.QuotientWitness source m H i)
    (hgood : D.IsGoodCompletelySplitReduction) :
    D.pointOfPEL hgood (Q.pullback D.nativeIntegralGeometricFrobenius).target =
      D.frobeniusPoint (D.pointOfPEL hgood Q.target) := by
  change D.pointOfPEL hgood (Q.target.pullback D.nativeIntegralGeometricFrobenius) = _
  rw [D.nativeIntegralGeometricFrobenius_eq]
  exact D.pointOfPEL_frobenius hgood Q.target

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
