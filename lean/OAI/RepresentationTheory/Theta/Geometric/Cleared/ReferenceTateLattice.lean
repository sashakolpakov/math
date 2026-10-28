import OAI.RepresentationTheory.Theta.Geometric.Cleared.ReferenceTateMap
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition

/-! # Reference Tate Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The full and individual preimage lattices of the actual cleared
reference isogeny are the literal inverse local matrix lattices. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}

def Data.ActiveHeckeThetaData.clearedLocalPreimage (g : D.RationalSU) (n : ℕ) (v : Fin s × Bool) :
    Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  (Data.ActiveHeckeThetaData.standardLocalLattice (q := q)).comap
    (((q : ℚ_[q]) ^ n • (D.localMatrix v g).val.mulVecLin).restrictScalars ℤ_[q])

variable (M : D.PeriodModel hg x) (F : D.ReferenceAnalyticFiber x)
    (N : D.PeriodModel hg y) (G : D.ReferenceAnalyticFiber y)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates)
    (f : M.abelian.toOver ⟶ N.abelian.toOver) [IsMonHom f] (n : ℕ) (g : D.RationalSU)
    (ht : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift f ((M.toNativeReferenceModel F).nativeReferenceMarking u) =
      (N.toNativeReferenceModel G).nativeReferenceMarking ((q : ℤ) ^ n • D.rationalLinear g u))

attribute [local irreducible] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame

include hc ht in
theorem Data.ActiveHeckeThetaData.cleared_reference_preimage_mem_iff
    (u : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateModule M.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q) :
    u ∈ AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f ↔
      ∀ v, M.referenceTateFrame F hgood hdegree u v ∈ Data.ActiveHeckeThetaData.clearedLocalPreimage g n v := by
  change AlgebraicGeometry.AbelianScheme.TateComparison.Rational.rationalTateMap (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f u ∈
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage N.abelian.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q ↔ _
  rw [N.referenceTateFrame_integral_mem_iff G hgood hdegree hc]
  simp only [Data.ActiveHeckeThetaData.cleared_referenceTateMap_apply M F N G hgood hdegree hc f n g ht]
  rfl

include hc ht in
theorem Data.ActiveHeckeThetaData.cleared_reference_full_preimage :
    (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.isogenyTatePreimage (T := Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (q := q) f).map
      ((M.referenceTateFrame F hgood hdegree).toLinearMap.restrictScalars ℤ_[q]) =
      Submodule.pi Set.univ (Data.ActiveHeckeThetaData.clearedLocalPreimage g n) := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩ v _
    exact (Data.ActiveHeckeThetaData.cleared_reference_preimage_mem_iff M F N G hgood hdegree hc f n g ht w).mp hw v
  · intro hu
    refine ⟨(M.referenceTateFrame F hgood hdegree).symm u, ?_,
      (M.referenceTateFrame F hgood hdegree).apply_symm_apply u⟩
    apply (Data.ActiveHeckeThetaData.cleared_reference_preimage_mem_iff M F N G hgood hdegree hc f n g ht _).mpr
    rw [LinearEquiv.apply_symm_apply]
    exact fun v => hu v (Set.mem_univ v)

include hc ht in
theorem Data.ActiveHeckeThetaData.cleared_reference_framed_lattice (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (M.referenceTateFrame F hgood hdegree) f v = Data.ActiveHeckeThetaData.clearedLocalPreimage g n v := by
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice, Data.ActiveHeckeThetaData.cleared_reference_full_preimage M F N G hgood hdegree hc f n g ht]
  exact AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition.submodule_pi_map_proj (Data.ActiveHeckeThetaData.clearedLocalPreimage g n) v

end

end OAI.RepresentationTheory.Theta.Geometric
