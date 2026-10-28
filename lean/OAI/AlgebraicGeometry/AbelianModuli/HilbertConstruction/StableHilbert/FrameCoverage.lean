import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FrameOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Frame Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FrameCoverage.StableHilbertCoverage

noncomputable section

/-! Geometrically sparse, nonzero vector configurations are covered by
the actual stable balanced frame charts. The cover consists of the
principal opens of their existing determinant denominators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u

variable {S : Scheme.{u}} {r m : ℕ}

def frameDenominator (v : Fin m → Fin r → Γ(S, ⊤))
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) : Γ(S, ⊤) :=
  Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent

theorem frameDenominator_map {A : Type u} [CommRing A]
    (φ : Γ(S, ⊤) →+* A) (v : Fin m → Fin r → Γ(S, ⊤))
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    φ (frameDenominator v j) =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k => φ (v z k))) j.exponent := by
  rw [frameDenominator, MonomialExponentExtension.exponentMonomial_map]
  congr 1
  funext τ
  exact LabeledDeterminantPolynomials.labeledDeterminant_map φ τ v

variable (v : Fin m → Fin r → Γ(S, ⊤)) (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hnonzero : ∀ (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S),
      ∀ z, (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (v z k)) ≠ 0)
    (hsparse : ∀ (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S),
      ∀ W : Submodule K (Fin r → K), W ≠ ⊤ →
        r * (Finset.univ.filter (fun z => (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (v z k)) ∈ W)).card < m)

include hr hm hnonzero hsparse in
theorem frameDenominators_cover (x : S) :
    ∃ j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r m, x ∈ S.basicOpen (frameDenominator v j) := by
  let K := AlgebraicClosure (S.residueField x)
  let q : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) K)) ≫ S.fromSpecResidueField x
  have hq : q (IsLocalRing.closedPoint K) = x := S.fromSpecResidueField_apply x _
  obtain ⟨j, hj⟩ := Stable.BalancedFrameIndex.sparseConfiguration_has_stableBalancedFrameIndex
    (fun z k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (v z k)) (hnonzero K q) hr hm (hsparse K q)
  have hu : IsUnit (Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (frameDenominator v j)) := by
    rw [frameDenominator_map]
    exact isUnit_iff_ne_zero.mpr hj
  exact ⟨j, hq ▸ Geometric.FrameOpenCover.fieldPoint_mem_basicOpen_of_unit q _ hu⟩

def frameOpenCover : Scheme.OpenCover.{0} S where
  I₀ := Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r m
  X j := (S.basicOpen (frameDenominator v j)).toScheme
  f j := (S.basicOpen (frameDenominator v j)).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨j, hj⟩ := frameDenominators_cover v hr hm hnonzero hsparse x
    exact ⟨j, ⟨⟨x, hj⟩, rfl⟩⟩

theorem frameOpenCover_denominator_unit (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial
      (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k =>
        ((frameOpenCover v hr hm hnonzero hsparse).f j).appTop (v z k))) j.exponent) := by
  let U := S.basicOpen (frameDenominator v j)
  have hp : U.ι ⁻¹ᵁ S.basicOpen (frameDenominator v j) = ⊤ := by
    ext x
    exact iff_true_intro x.property
  have hu : IsUnit (U.ι.appTop (frameDenominator v j)) :=
    (Scalar.Nonvanishing.global_isUnit_iff_basicOpen_eq_top _).mpr ((U.ι.preimage_basicOpen_top _).symm.trans hp)
  exact (frameDenominator_map U.ι.appTop.hom v j) ▸ hu

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FrameCoverage.StableHilbertCoverage
