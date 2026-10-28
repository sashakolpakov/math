import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockMaps
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ChosenTorsionKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockExactness

/-! # Polarized Block Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual polarized isogeny's Tate cokernel, restricted to each
split block, is its actual torsion-kernel block. The reverse map is proved
equivariant from its multiplier equations and the isogeny's equivariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {m : ℕ}
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m)) (δ : Fin (3 * s) → ℕ)
  (hδ : P.polarizationMap.HasPolarizationType δ) (hq : Nat.Coprime q (∏ i, δ i))

omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.tateReverse_comp_qpow :
    (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq).comp
      (Add.schemeTateMap P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q e.isogeny.hom) =
      (q : ℤ_[q]) ^ m • LinearMap.id := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact e.integralTateReverse_comp (𝟙 (Spec (.of k))) q δ hδ hq

omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.comp_tateReverse_qpow :
    (Add.schemeTateMap P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q e.isogeny.hom).comp
      (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq) =
      (q : ℤ_[q]) ^ m • LinearMap.id := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact e.comp_integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq

omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.tateReverse_splitAction_commute (a : Fin s × Bool → ℤ_[q]) :
    (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq).comp
      (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q a) =
    (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) P a).comp
      (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq) :=
  KernelQuotient.Tate.reverse_intertwines q
    (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toAdditive
    m (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq)
    (D.tateReverse_comp_qpow e δ hδ hq) (D.comp_tateReverse_qpow e δ hδ hq)
    _ _ (D.splitTateAction_commute h (Over.mk (𝟙 (Spec (.of k)))) e a)

def Data.SphericalPELAlbaneseData.polarizedTateBoundary :
    Add.schemeTateModule Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q →ₗ[ℤ_[q]]
      Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m :=
  (Evaluation.Tate.evaluate q m).comp (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq)

omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.polarizedTateBoundary_commute (a : Fin s × Bool → ℤ_[q]) :
    (D.polarizedTateBoundary e δ hδ hq).comp
      (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q a) =
    (D.splitTorsionAction h (Over.mk (𝟙 (Spec (.of k)))) P m a).comp
      (D.polarizedTateBoundary e δ hδ hq) := by
  rw [Data.SphericalPELAlbaneseData.polarizedTateBoundary, LinearMap.comp_assoc, D.tateReverse_splitAction_commute h,
    ← LinearMap.comp_assoc, D.evaluate_splitAction h, LinearMap.comp_assoc]

omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.polarizedTateBoundary_ker : (D.polarizedTateBoundary e δ hδ hq).ker =
    (Add.schemeTateMap P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q e.isogeny.hom).range :=
  KernelQuotient.Tate.boundary_raw_ker q
    (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toAdditive
    m (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq)
    (D.tateReverse_comp_qpow e δ hδ hq) (D.comp_tateReverse_qpow e δ hδ hq)

theorem Data.SphericalPELAlbaneseData.polarizedTateBoundary_range : (D.polarizedTateBoundary e δ hδ hq).range =
    (Add.Tate.mapLevel q
      (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toAdditive m).ker :=
  KernelQuotient.Tate.boundary_raw_range q
    (P.abelian.mapPoints Q.abelian e.isogeny.hom (Over.mk (𝟙 (Spec (.of k))))).toAdditive
    m (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq)
    (D.tateReverse_comp_qpow e δ hδ hq) (D.comp_tateReverse_qpow e δ hδ hq)
    (GeometricDivision.geometricPoint_divisible P.abelian q)

def Data.SphericalPELAlbaneseData.tateBlockCokernelEquivKernel (v : Fin s × Bool) :
    (↥(D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v) ⧸
      (D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v).range) ≃ₗ[ℤ_[q]]
      D.torsionKernelBlock h (Over.mk (𝟙 (Spec (.of k)))) e m v := by
  let c := BlockExactness.ProductAction.blockCokernelEquiv
    (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) P)
    (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q)
    (D.splitTorsionAction h (Over.mk (𝟙 (Spec (.of k)))) P m)
    (Add.schemeTateMap P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q e.isogeny.hom)
    (D.splitTateAction_commute h (Over.mk (𝟙 (Spec (.of k)))) e)
    (D.polarizedTateBoundary e δ hδ hq) (D.polarizedTateBoundary_commute h e δ hδ hq)
    (D.polarizedTateBoundary_ker e δ hδ hq) v
  exact c.trans (LinearEquiv.ofEq _ _ (by rw [D.polarizedTateBoundary_range]; rfl))

def Data.SphericalPELAlbaneseData.tateBlockCokernelEquivChosenKernel (v : Fin s × Bool) :
    (↥(D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v) ⧸
      (D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v).range) ≃+
    Additive (((Subgroups.PointSubgroup.kernel e.isogeny.hom).inf
      (Subgroups.splitBlock P (D.localCharacter v) m)).atTest (Over.mk (𝟙 (Spec (.of k))))) :=
  (D.tateBlockCokernelEquivKernel h e δ hδ hq v).toAddEquiv.trans
    (D.chosenTorsionKernelEquiv h (Over.mk (𝟙 (Spec (.of k)))) e m v)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
