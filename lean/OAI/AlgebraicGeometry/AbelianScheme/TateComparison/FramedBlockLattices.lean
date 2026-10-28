import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FrameBlockCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BlockLatticeBounds

/-! # Framed Block Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! Coordinates of actual target-block preimages in a source PEL frame.
The multiplier equation transfers completed equivariance through the
actual rational isogeny inverse. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k] {m : ℕ}
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (frame : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
  (hf : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (δ : Fin (3 * s) → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

def Data.SphericalPELAlbaneseData.rationalFrameCoordinate (v : Fin s × Bool) (i : Fin 3) :
    Rational.rationalTateModule P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q →ₗ[ℤ_[q]] ℚ_[q] :=
  (LinearMap.proj i).comp ((LinearMap.proj v).comp (frame.restrictScalars ℤ_[q]).toLinearMap)

def Data.SphericalPELAlbaneseData.preimageFrameCoordinate (v : Fin s × Bool) (i : Fin 3) :
    Add.schemeTateModule Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q →ₗ[ℤ_[q]] ℚ_[q] :=
  (D.rationalFrameCoordinate frame v i).comp
    ((Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom).subtype.comp
      (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny).toLinearMap)

theorem Data.SphericalPELAlbaneseData.preimageFrameCoordinate_apply (v : Fin s × Bool) (i : Fin 3)
    (y : Add.schemeTateModule Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    D.preimageFrameCoordinate e frame v i y =
      frame (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny y).val v i := rfl

theorem Data.SphericalPELAlbaneseData.preimageFrameCoordinate_multiplier (v : Fin s × Bool) (i : Fin 3)
    (y : Add.schemeTateModule Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q) :
    (q : ℤ_[q]) ^ m • D.preimageFrameCoordinate e frame v i y =
      D.integralFrameCoordinate (Over.mk (𝟙 (Spec (.of k)))) P frame v i
        (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq y) := by
  have he := congrArg (D.rationalFrameCoordinate frame v i)
    (e.targetTatePreimage_multiplier (𝟙 (Spec (.of k))) q δ hδ hq y)
  rw [map_smul, Nat.cast_pow] at he
  exact he

include hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.preimageFrameCoordinate_split (a : Fin s × Bool → ℤ_[q])
    (y : Add.schemeTateModule Q.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
    (v : Fin s × Bool) (i : Fin 3) :
    D.preimageFrameCoordinate e frame v i (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q a y) =
      a v • D.preimageFrameCoordinate e frame v i y := by
  have hn : (q : ℤ_[q]) ^ m ≠ 0 := pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  apply smul_right_injective (M := ℚ_[q]) hn
  dsimp only
  rw [D.preimageFrameCoordinate_multiplier e frame δ hδ hq]
  have hy := congrArg (fun f => f y) (D.tateReverse_splitAction_commute h e δ hδ hq a)
  change e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq
      (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q a y) =
    D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) P a
      (e.integralTateReverse (𝟙 (Spec (.of k))) q δ hδ hq y) at hy
  rw [hy, D.integralFrameCoordinate_split h _ P frame hf, smul_comm,
    D.preimageFrameCoordinate_multiplier e frame δ hδ hq]

include hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.preimageFrameCoordinate_off_block {w v : Fin s × Bool} (hwv : w ≠ v)
    (y : D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q w) (i : Fin 3) :
    frame (D.targetBlockToTateSpace h (𝟙 (Spec (.of k))) e w y) v i = 0 := by
  classical
  have hy := D.preimageFrameCoordinate_split h e frame hf δ hδ hq (Pi.single w 1) y.val v i
  rw [← ProductActionDecomposition.ProductAction.projector_eq_single,
    ProductActionDecomposition.ProductAction.projector_on_block (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q) w y,
    Pi.single_eq_of_ne hwv.symm, zero_smul, D.preimageFrameCoordinate_apply] at hy
  exact hy

end

/-! The lattice projected in the statement's source frame is exactly the
image of the corresponding actual target Tate block. The coordinate map
on that block is injective; no other block contributes to its coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {k : Type} [Field k] [IsAlgClosed k] {m : ℕ}
  {P Q : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level (Spec (.of k))}
  (e : PELIsogenies.PELIsogeny P Q (q ^ m))
  (frame : Rational.SplitTateFrame s P.abelian.scheme (Over.mk (𝟙 (Spec (.of k)))) q)
  (hf : Rational.IsSplitActionFrame P (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (δ : Fin (3 * s) → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

def Data.SphericalPELAlbaneseData.framedTargetBlockMap (v : Fin s × Bool) :
    D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v →ₗ[ℤ_[q]] (Fin 3 → ℚ_[q]) :=
  LinearMap.pi fun i => (D.preimageFrameCoordinate e frame v i).comp
    (D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v).subtype

theorem Data.SphericalPELAlbaneseData.framedTargetBlockMap_apply (v : Fin s × Bool)
    (y : D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v) (i : Fin 3) :
    D.framedTargetBlockMap h e frame v y i =
      frame (D.targetBlockToTateSpace h (𝟙 (Spec (.of k))) e v y) v i := rfl

include hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.framedTargetBlockMap_injective (v : Fin s × Bool) :
    Function.Injective (D.framedTargetBlockMap h e frame v) := by
  intro x y hxy
  apply D.targetBlockToTateSpace_injective h (𝟙 (Spec (.of k))) e v
  apply frame.injective
  funext w i
  by_cases hw : w = v
  · subst w
    simpa only [D.framedTargetBlockMap_apply] using congrFun hxy i
  · rw [D.preimageFrameCoordinate_off_block h e frame hf δ hδ hq (Ne.symm hw) x i,
      D.preimageFrameCoordinate_off_block h e frame hf δ hδ hq (Ne.symm hw) y i]

include hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.framedTargetBlockMap_range (v : Fin s × Bool) :
    (D.framedTargetBlockMap h e frame v).range = Rational.framedTateLattice frame e.isogeny.hom v := by
  classical
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨frame (D.targetBlockToTateSpace h (𝟙 (Spec (.of k))) e v y), ?_, rfl⟩
    refine ⟨D.targetBlockToTateSpace h (𝟙 (Spec (.of k))) e v y, ?_, rfl⟩
    exact (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny y.val).property
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    let t : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom := ⟨w, hw⟩
    let y := (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny).symm t
    have hy : PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny y = t :=
      (PreimageQuotient.targetTatePreimageEquiv (𝟙 (Spec (.of k))) q e.isogeny).apply_symm_apply t
    let a : D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v :=
      ⟨ProductActionDecomposition.ProductAction.projector (D.splitTateAction h (Over.mk (𝟙 (Spec (.of k)))) Q) v y, ⟨y, rfl⟩⟩
    refine ⟨a, ?_⟩
    funext i
    have hp := D.preimageFrameCoordinate_split h e frame hf δ hδ hq (Pi.single v 1) y v i
    rw [← ProductActionDecomposition.ProductAction.projector_eq_single, Pi.single_eq_same, one_smul] at hp
    change D.preimageFrameCoordinate e frame v i a.val = frame w v i
    exact hp.trans (by rw [D.preimageFrameCoordinate_apply, hy])

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
