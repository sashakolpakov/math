import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Integral
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # Moduli Point -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel

noncomputable section

section

/-!
Geometric points and ordinary points of the actual integral PEL reduction.
Frobenius is independently defined by the q-power field automorphism.
Ordinarity is maximal geometric q-rank; preservation by Frobenius is proved
by transport of the entire torsion group, not included in the point type.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
variable {q : ℕ} [Fact q.Prime]

abbrev ModuliPoint.Construction.residueClosure (q : ℕ) [Fact q.Prime] := AlgebraicClosure (ZMod q)

def ModuliPoint.Construction.geometricBase (q : ℕ) [Fact q.Prime] : Over (Spec (.of (ZMod q))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q))))

/-- The q-power automorphism of the algebraic closure, over F_q. -/
def ModuliPoint.Construction.geometricBaseFrobenius (q : ℕ) [Fact q.Prime] :
    ModuliPoint.Construction.geometricBase q ≅ ModuliPoint.Construction.geometricBase q := by
  let σ := FiniteField.frobeniusAlgEquiv (ZMod q) (ModuliPoint.Construction.residueClosure q) q
  refine Over.isoMk (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q))) =
    Spec.map (CommRingCat.ofHom (algebraMap (ZMod q) (ModuliPoint.Construction.residueClosure q)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact σ.commutes a

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

def Integral.Construction.SplitPELReduction.GeometricPoint := ModuliPoint.Construction.geometricBase q ⟶ D.specialFiber

/-- The geometric point of the moduli scheme obtained by q-power Frobenius. -/
def Integral.Construction.SplitPELReduction.frobeniusPoint (x : D.GeometricPoint) : D.GeometricPoint :=
  (ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ x

/-- The actual geometric q-torsion group at a moduli point. -/
abbrev Integral.Construction.SplitPELReduction.geometricTorsion (x : D.GeometricPoint) :=
  D.abelian.torsionPoints q (Over.mk x.left)

/-- Ordinary means maximal geometric q-rank, for an abelian variety of
dimension 3s. No Frobenius-kernel identity is included here. -/
def Integral.Construction.SplitPELReduction.IsOrdinary (x : D.GeometricPoint) : Prop :=
  Nat.card (D.geometricTorsion x) = q ^ (3 * s)

def Integral.Construction.SplitPELReduction.OrdinaryPoint := {x : D.GeometricPoint // D.IsOrdinary x}

def Integral.Construction.SplitPELReduction.frobeniusTestIso (x : D.GeometricPoint) :
    Over.mk (D.frobeniusPoint x).left ≅ Over.mk x.left :=
  Over.isoMk ((Over.forget _).mapIso (ModuliPoint.Construction.geometricBaseFrobenius q)) rfl

/-- Transport along the field automorphism preserves geometric torsion. -/
def Integral.Construction.SplitPELReduction.frobeniusTorsionEquiv (x : D.GeometricPoint) :
    D.geometricTorsion x ≃* D.geometricTorsion (D.frobeniusPoint x) :=
  ((D.abelian.torsionFunctor q).mapIso (D.frobeniusTestIso x).op).groupIsoToMulEquiv

theorem Integral.Construction.SplitPELReduction.frobenius_preserves_ordinarity (x : D.GeometricPoint) :
    D.IsOrdinary (D.frobeniusPoint x) ↔ D.IsOrdinary x := by
  unfold Integral.Construction.SplitPELReduction.IsOrdinary
  rw [← Nat.card_congr (D.frobeniusTorsionEquiv x).toEquiv]

def Integral.Construction.SplitPELReduction.ordinaryFrobenius (x : D.OrdinaryPoint) : D.OrdinaryPoint :=
  ⟨D.frobeniusPoint x.val, (D.frobenius_preserves_ordinarity x.val).mpr x.property⟩

end

/-!
Classifying a constructed polarized integral-action datum on a geometric
special fiber. The good-reduction input is IntegralModel's actual fine-moduli
property on reduced tests. The special-fiber point is constructed by the
scheme pullback adjunction; no classifying map or comparison is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
variable {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s}
variable {iota : E →+* K} {κ : K →+* ℂ}
variable {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
variable {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ} {q : ℕ} [Fact q.Prime]

variable (D : Integral.Construction.SplitPELReduction P iota κ M U B q)

/-- The remaining good-reduction clause: the actual integral family
classifies PEL data on reduced test schemes. Smoothness and split local
coefficients are already in the native reduction data. -/
def Integral.Construction.SplitPELReduction.IsGoodCompletelySplitReduction : Prop := D.integral.IsReducedPELModuli

def Integral.Construction.SplitPELReduction.integralGeometricBase : Over B.base :=
  (Over.map D.specialBase).obj (ModuliPoint.Construction.geometricBase q)

/-- A complete PEL datum on the geometric special fiber, regarded as an
object over the genuine integral arithmetic base. -/
abbrev Integral.Construction.SplitPELReduction.GeometricPELDatum :=
  PELModuli.IntegralModel.PEL.Has.IntegralPELObject P B.R (B.integralEmbedding iota) N D.integralGeometricBase

/-- The pullback adjunction relates actual points of the special fiber
to integral-base morphisms from the same geometric field. -/
def Integral.Construction.SplitPELReduction.geometricPointIntegralEquiv :
    D.GeometricPoint ≃ (D.integralGeometricBase ⟶ D.integral.toOver) :=
  ((Over.mapPullbackAdj D.specialBase).homEquiv (ModuliPoint.Construction.geometricBase q) D.integral.toOver).symm

def Integral.Construction.SplitPELReduction.PointClassifies (x : D.GeometricPoint) (A : D.GeometricPELDatum) : Prop :=
  Nonempty (PELModuli.IntegralModel.PEL.Has.PulledBackPELDataIso D.integral.universal.data A.data
    (D.geometricPointIntegralEquiv x).left (𝟙 D.integralGeometricBase.left))

theorem Integral.Construction.SplitPELReduction.existsUnique_classifyingPoint
    (hgood : D.IsGoodCompletelySplitReduction) (A : D.GeometricPELDatum) :
    ∃! x : D.GeometricPoint, D.PointClassifies x A := by
  have : IsReduced D.integralGeometricBase.left :=
    inferInstanceAs (IsReduced (Spec (.of (ModuliPoint.Construction.residueClosure q))))
  obtain ⟨f, hf, huniq⟩ := hgood D.integralGeometricBase A
  refine ⟨D.geometricPointIntegralEquiv.symm f, ?_, ?_⟩
  · change Nonempty (PELModuli.IntegralModel.PEL.Has.PulledBackPELDataIso D.integral.universal.data A.data
      (D.geometricPointIntegralEquiv (D.geometricPointIntegralEquiv.symm f)).left
        (𝟙 D.integralGeometricBase.left))
    exact (D.geometricPointIntegralEquiv.apply_symm_apply f).symm ▸ hf
  · intro x hx
    apply D.geometricPointIntegralEquiv.injective
    exact (huniq _ hx).trans (D.geometricPointIntegralEquiv.apply_symm_apply f).symm

/-- Construct a geometric moduli point from the full quotient datum once
the geometric quotient, action, polarization, and signature have been built. -/
def Integral.Construction.SplitPELReduction.pointOfPEL (hgood : D.IsGoodCompletelySplitReduction) (A : D.GeometricPELDatum) :
    D.GeometricPoint := (D.existsUnique_classifyingPoint hgood A).choose

theorem Integral.Construction.SplitPELReduction.pointOfPEL_classifies (hgood : D.IsGoodCompletelySplitReduction)
    (A : D.GeometricPELDatum) : D.PointClassifies (D.pointOfPEL hgood A) A :=
  (D.existsUnique_classifyingPoint hgood A).choose_spec.1

/-- Equality of full classified data determines the geometric moduli point. -/
theorem Integral.Construction.SplitPELReduction.pointOfPEL_eq_of_classifies (hgood : D.IsGoodCompletelySplitReduction)
    (A : D.GeometricPELDatum) (x : D.GeometricPoint) (hx : D.PointClassifies x A) :
    D.pointOfPEL hgood A = x :=
  ((D.existsUnique_classifyingPoint hgood A).choose_spec.2 x hx).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel
