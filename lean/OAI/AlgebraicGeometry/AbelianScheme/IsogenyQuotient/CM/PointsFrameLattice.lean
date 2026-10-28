import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsTateBlocks
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeTransport

/-! # Points Frame Lattice -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsFrameLattice.Construction

noncomputable section

/-!
An action-compatible rational frame identifies each actual integral
CMPoints Tate block with the projected source lattice. Fullness of the source
lattice then constructs a rank-three integral basis of that block.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E L : Type} [Field E] [NumberField E] [IsGalois ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {g N : ℕ} (T : Over S)
  (F : TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (frame : TateComparison.Rational.rationalTateModule F.abelian.scheme T q ≃ₗ[ℚ_[q]] (Fin 3 → Gal(E/ℚ) → ℚ_[q]))
  (hf : ∀ (a : NumberField.RingOfIntegers E) (z : TateComparison.Rational.rationalTateModule F.abelian.scheme T q)
    (i : Fin 3) (τ : Gal(E/ℚ)),
    frame (TateComparison.Rational.rationalTateMap (T := T) (q := q) (TateComparison.End.endSchemeMap F.abelian.scheme (F.action a)) z) i τ =
      (j.localCharacter iota τ a : ℚ_[q]) * frame z i τ)

def l45IntegralFrameCoordinate (i : Fin 3) (τ : Gal(E/ℚ)) :
    TateComparison.Add.schemeTateModule F.abelian.scheme T q →ₗ[ℤ_[q]] ℚ_[q] :=
  ((LinearMap.proj τ).comp ((LinearMap.proj i).comp (frame.restrictScalars ℤ_[q]).toLinearMap)).comp
    (TensorProduct.mk ℤ_[q] ℚ_[q] (TateComparison.Add.schemeTateModule F.abelian.scheme T q) 1)

omit [IsGalois ℚ E] in
include hf in
theorem l45IntegralFrameCoordinate_action (a : NumberField.RingOfIntegers E)
    (x : TateComparison.Add.schemeTateModule F.abelian.scheme T q) (i : Fin 3) (τ : Gal(E/ℚ)) :
    l45IntegralFrameCoordinate T F frame i τ (TateComparison.TateAction.tateIntegralAction T q F a x) =
      j.localCharacter iota τ a • l45IntegralFrameCoordinate T F frame i τ x := by
  have hx := hf a (1 ⊗ₜ[ℤ_[q]] x) i τ
  rw [TateComparison.Lattices.rationalTateMap_integral] at hx
  change frame (1 ⊗ₜ[ℤ_[q]] (TateComparison.TateAction.tateEndMap F.abelian.scheme T q (F.action a)) x) i τ = _
  rw [TateComparison.TateAction.tateEndMap_eq_schemeTateMap]
  exact hx

omit [IsGalois ℚ E] in
include hf in
theorem l45IntegralFrameCoordinate_completed (a : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E)
    (x : TateComparison.Add.schemeTateModule F.abelian.scheme T q) (i : Fin 3) (τ : Gal(E/ℚ)) :
    l45IntegralFrameCoordinate T F frame i τ (TateComparison.TateAction.tateCompletedAction T q F a x) =
      SplitCompletion.Construction.l45CompletionMap j iota a τ • l45IntegralFrameCoordinate T F frame i τ x := by
  induction a using TensorProduct.inductionOn with
  | tmul z r =>
    rw [TateComparison.TateAction.tateCompletedAction_tmul]
    change l45IntegralFrameCoordinate T F frame i τ (z • TateComparison.TateAction.tateIntegralAction T q F r x) =
      (z * j.localCharacter iota τ r) • l45IntegralFrameCoordinate T F frame i τ x
    rw [map_smul, l45IntegralFrameCoordinate_action j iota T F frame hf, mul_smul]
  | add a b ha hb =>
    rw [map_add, LinearMap.add_apply, map_add, ha, hb, map_add]
    exact (add_smul _ _ _).symm

include hf in
theorem l45IntegralFrameCoordinate_split (a : Gal(E/ℚ) → ℤ_[q])
    (x : TateComparison.Add.schemeTateModule F.abelian.scheme T q) (i : Fin 3) (τ : Gal(E/ℚ)) :
    l45IntegralFrameCoordinate T F frame i τ (PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit T F a x) =
      a τ • l45IntegralFrameCoordinate T F frame i τ x := by
  have hx := l45IntegralFrameCoordinate_completed j iota T F frame hf
    ((SplitCompletion.Construction.l45CompletionEquiv j iota hsplit).symm a) x i τ
  change l45IntegralFrameCoordinate T F frame i τ (PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit T F a x) =
    SplitCompletion.Construction.l45CompletionEquiv j iota hsplit ((SplitCompletion.Construction.l45CompletionEquiv j iota hsplit).symm a) τ •
      l45IntegralFrameCoordinate T F frame i τ x at hx
  rwa [AlgEquiv.apply_symm_apply] at hx

include hf in
theorem l45IntegralFrameCoordinate_off_block {υ τ : Gal(E/ℚ)} (hυ : υ ≠ τ)
    (x : PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit T F υ) (i : Fin 3) :
    frame (1 ⊗ₜ[ℤ_[q]] x.val) i τ = 0 := by
  classical
  have hx := l45IntegralFrameCoordinate_split j iota hsplit T F frame hf (Pi.single υ 1) x.val i τ
  rw [← TateComparison.ProductActionDecomposition.ProductAction.projector_eq_single,
    TateComparison.ProductActionDecomposition.ProductAction.projector_on_block (PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit T F) υ x,
    Pi.single_eq_of_ne hυ.symm, zero_smul] at hx
  exact hx

def l45FrameBlockProjection (τ : Gal(E/ℚ)) : (Fin 3 → Gal(E/ℚ) → ℚ_[q]) →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q]) :=
  LinearMap.pi fun i => (LinearMap.proj τ : (Gal(E/ℚ) → ℚ_[q]) →ₗ[ℚ_[q]] ℚ_[q]).comp
    (LinearMap.proj i : (Fin 3 → Gal(E/ℚ) → ℚ_[q]) →ₗ[ℚ_[q]] (Gal(E/ℚ) → ℚ_[q]))

def l45FramedSourceLattice (τ : Gal(E/ℚ)) : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  ((TateComparison.Rational.integralTateImage F.abelian.scheme T q).map (frame.restrictScalars ℤ_[q]).toLinearMap).map
    ((l45FrameBlockProjection (q := q) τ).restrictScalars ℤ_[q])

omit [IsGalois ℚ E] in
theorem l45FramedSourceLattice_isLattice
    [Submodule.IsLattice ℚ_[q] (TateComparison.Rational.integralTateImage F.abelian.scheme T q)] (τ : Gal(E/ℚ)) :
    Submodule.IsLattice ℚ_[q] (l45FramedSourceLattice T F frame τ) := by
  have : Submodule.IsLattice ℚ_[q]
      ((TateComparison.Rational.integralTateImage F.abelian.scheme T q).map (frame.restrictScalars ℤ_[q]).toLinearMap) :=
    TateComparison.LatticeTransport.isLattice_map_surjective (TateComparison.Rational.integralTateImage F.abelian.scheme T q) frame.toLinearMap frame.surjective
  exact TateComparison.LatticeTransport.isLattice_map_surjective _ (l45FrameBlockProjection (q := q) τ)
    (fun z => ⟨fun i _ => z i, rfl⟩)

def l45FramedSourceBlockMap (τ : Gal(E/ℚ)) :
    PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit T F τ →ₗ[ℤ_[q]] (Fin 3 → ℚ_[q]) :=
  LinearMap.pi fun i => (l45IntegralFrameCoordinate T F frame i τ).comp
    (PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit T F τ).subtype

include hf in
theorem l45FramedSourceBlockMap_injective (τ : Gal(E/ℚ)) :
    Function.Injective (l45FramedSourceBlockMap j iota hsplit T F frame τ) := by
  intro x y hxy
  apply Subtype.ext
  apply TateComparison.Isogeny.Tate.integralEmbedding_injective q
  change 1 ⊗ₜ[ℤ_[q]] x.val = 1 ⊗ₜ[ℤ_[q]] y.val
  apply frame.injective
  funext i υ
  by_cases h : υ = τ
  · subst υ
    exact congrFun hxy i
  · rw [l45IntegralFrameCoordinate_off_block j iota hsplit T F frame hf (Ne.symm h) x i,
      l45IntegralFrameCoordinate_off_block j iota hsplit T F frame hf (Ne.symm h) y i]

include hf in
theorem l45FramedSourceBlockMap_range (τ : Gal(E/ℚ)) :
    (l45FramedSourceBlockMap j iota hsplit T F frame τ).range = l45FramedSourceLattice T F frame τ := by
  classical
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨frame (1 ⊗ₜ[ℤ_[q]] x.val), ⟨1 ⊗ₜ[ℤ_[q]] x.val, ⟨x.val, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    let y : PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit T F τ :=
      ⟨TateComparison.ProductActionDecomposition.ProductAction.projector (PointsTateBlocks.Construction.l45SplitTateAction j iota hsplit T F) τ x, ⟨x, rfl⟩⟩
    refine ⟨y, ?_⟩
    funext i
    have hx := l45IntegralFrameCoordinate_split j iota hsplit T F frame hf (Pi.single τ 1) x i τ
    rw [← TateComparison.ProductActionDecomposition.ProductAction.projector_eq_single, Pi.single_eq_same, one_smul] at hx
    exact hx

def l45FramedSourceBlockEquiv (τ : Gal(E/ℚ)) :
    PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit T F τ ≃ₗ[ℤ_[q]] l45FramedSourceLattice T F frame τ :=
  (LinearEquiv.ofInjective (l45FramedSourceBlockMap j iota hsplit T F frame τ)
    (l45FramedSourceBlockMap_injective j iota hsplit T F frame hf τ)).trans
      (LinearEquiv.ofEq _ _ (l45FramedSourceBlockMap_range j iota hsplit T F frame hf τ))

def l45TateBlockBasisOfFrame
    [Submodule.IsLattice ℚ_[q] (TateComparison.Rational.integralTateImage F.abelian.scheme T q)] (τ : Gal(E/ℚ)) :
    Module.Basis (Fin 3) ℤ_[q] (PointsTateBlocks.Construction.l45IntegralTateBlock j iota hsplit T F τ) := by
  have := l45FramedSourceLattice_isLattice T F frame τ
  have hr : Module.finrank ℤ_[q] (l45FramedSourceLattice T F frame τ) = 3 := by
    simpa using Submodule.IsLattice.finrank_of_pi ℚ_[q] (l45FramedSourceLattice T F frame τ)
  exact (Module.finBasisOfFinrankEq ℤ_[q] (l45FramedSourceLattice T F frame τ) hr).map
    (l45FramedSourceBlockEquiv j iota hsplit T F frame hf τ).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsFrameLattice.Construction
