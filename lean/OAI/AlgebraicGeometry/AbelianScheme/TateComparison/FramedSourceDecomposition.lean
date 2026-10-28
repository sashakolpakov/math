import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FrameBlockCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LatticeTransport

/-! # Framed Source Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

section

/-! The projected source lattice is the image of its actual integral
Tate block. Under the statement's integral-frame condition this is exactly
the prescribed initial chosen lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

theorem FramedSourceDecomposition.submodule_pi_map_proj {R V I : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (L : I → Submodule R V) (v : I) :
    (Submodule.pi Set.univ L).map (LinearMap.proj v) = L v := by
  classical
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx v (Set.mem_univ v)
  · intro hz
    refine ⟨Pi.single v z, ?_, by simp⟩
    intro w _
    change (Pi.single v z : I → V) w ∈ L w
    by_cases hw : w = v
    · subst w
      simpa only [Pi.single_eq_same] using hz
    · simp only [Pi.single_eq_of_ne hw, Submodule.zero_mem]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (h : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (P : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
  (frame : Rational.SplitTateFrame s P.abelian.scheme T q)
  (hf : Rational.IsSplitActionFrame P T q D.localCharacter frame)

def Data.SphericalPELAlbaneseData.framedSourceBlockMap (v : Fin s × Bool) :
    D.integralTateBlock h T P v →ₗ[ℤ_[q]] (Fin 3 → ℚ_[q]) :=
  LinearMap.pi fun i => (D.integralFrameCoordinate T P frame v i).comp
    (D.integralTateBlock h T P v).subtype

theorem Data.SphericalPELAlbaneseData.framedSourceBlockMap_apply (v : Fin s × Bool) (x : D.integralTateBlock h T P v) (i : Fin 3) :
    D.framedSourceBlockMap h T P frame v x i = frame (1 ⊗ₜ[ℤ_[q]] x.val) v i := rfl

def Data.SphericalPELAlbaneseData.framedSourceLattice (v : Fin s × Bool) : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  (Rational.framedIntegralTateImage frame).map
    ((LinearMap.proj v : Rational.SplitTateSpace s q →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q])).restrictScalars ℤ_[q])

theorem Data.SphericalPELAlbaneseData.framedSourceLattice_isLattice
    [Submodule.IsLattice ℚ_[q] (Rational.integralTateImage P.abelian.scheme T q)] (v : Fin s × Bool) :
    Submodule.IsLattice ℚ_[q] (D.framedSourceLattice T P frame v) := by
  have : Submodule.IsLattice ℚ_[q] (Rational.framedIntegralTateImage frame) :=
    LatticeTransport.isLattice_map_surjective (Rational.integralTateImage P.abelian.scheme T q) frame.toLinearMap frame.surjective
  exact LatticeTransport.isLattice_map_surjective (Rational.framedIntegralTateImage frame) (LinearMap.proj v)
    (fun z => ⟨fun _ => z, rfl⟩)

include hf in
theorem Data.SphericalPELAlbaneseData.framedSourceBlockMap_injective (v : Fin s × Bool) :
    Function.Injective (D.framedSourceBlockMap h T P frame v) := by
  intro x y hxy
  apply Subtype.ext
  apply Isogeny.Tate.integralEmbedding_injective q
  change 1 ⊗ₜ[ℤ_[q]] x.val = 1 ⊗ₜ[ℤ_[q]] y.val
  apply frame.injective
  funext w i
  by_cases hw : w = v
  · subst w
    simpa only [D.framedSourceBlockMap_apply] using congrFun hxy i
  · rw [D.integralFrameCoordinate_off_block h T P frame hf (Ne.symm hw) x i,
      D.integralFrameCoordinate_off_block h T P frame hf (Ne.symm hw) y i]

include hf in
theorem Data.SphericalPELAlbaneseData.framedSourceBlockMap_range (v : Fin s × Bool) :
    (D.framedSourceBlockMap h T P frame v).range = D.framedSourceLattice T P frame v := by
  classical
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨frame (1 ⊗ₜ[ℤ_[q]] x.val), ⟨1 ⊗ₜ[ℤ_[q]] x.val, ⟨x.val, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    let a : D.integralTateBlock h T P v :=
      ⟨ProductActionDecomposition.ProductAction.projector (D.splitTateAction h T P) v x, ⟨x, rfl⟩⟩
    refine ⟨a, ?_⟩
    funext i
    have hx := D.integralFrameCoordinate_split h T P frame hf (Pi.single v 1) x v i
    rw [← ProductActionDecomposition.ProductAction.projector_eq_single, Pi.single_eq_same, one_smul] at hx
    exact hx

theorem Data.SphericalPELAlbaneseData.framedSourceLattice_eq_pi
    (L : Fin s × Bool → Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (hL : Rational.framedIntegralTateImage frame = Submodule.pi Set.univ L) (v : Fin s × Bool) :
    D.framedSourceLattice T P frame v = L v := by
  rw [Data.SphericalPELAlbaneseData.framedSourceLattice, hL]
  exact FramedSourceDecomposition.submodule_pi_map_proj L v

end

/-! A compatible frame identifies the actual integral Tate image with
the product of its projected lattices. No integral-frame equality is
assumed. Each projected lattice is the actual corresponding Tate block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  {S : Scheme} (T : Over S)
  (P : PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) D.level S)
  (frame : Rational.SplitTateFrame s P.abelian.scheme T q)
  (hf : Rational.IsSplitActionFrame P T q D.localCharacter frame)

def Data.SphericalPELAlbaneseData.framedSourceBlockEquiv (v : Fin s × Bool) :
    D.integralTateBlock hg T P v ≃ₗ[ℤ_[q]] D.framedSourceLattice T P frame v :=
  (LinearEquiv.ofInjective (D.framedSourceBlockMap hg T P frame v)
    (D.framedSourceBlockMap_injective hg T P frame hf v)).trans
      (LinearEquiv.ofEq _ _ (D.framedSourceBlockMap_range hg T P frame hf v))

include hg hf in
theorem Data.SphericalPELAlbaneseData.framedSourceLattice_single_mem (v : Fin s × Bool)
    (z : Fin 3 → ℚ_[q]) (hz : z ∈ D.framedSourceLattice T P frame v) :
    (Pi.single v z : Rational.SplitTateSpace s q) ∈ Rational.framedIntegralTateImage frame := by
  classical
  rw [← D.framedSourceBlockMap_range hg T P frame hf v] at hz
  obtain ⟨a, rfl⟩ := hz
  refine ⟨1 ⊗ₜ[ℤ_[q]] a.val, ⟨a.val, rfl⟩, ?_⟩
  funext w i
  change frame (1 ⊗ₜ[ℤ_[q]] a.val) w i =
    (Pi.single v (D.framedSourceBlockMap hg T P frame v a) : Rational.SplitTateSpace s q) w i
  by_cases hw : w = v
  · subst w
    simp only [Pi.single_eq_same, Data.SphericalPELAlbaneseData.framedSourceBlockMap_apply]
  · rw [D.integralFrameCoordinate_off_block hg T P frame hf (Ne.symm hw) a i]
    simp only [Pi.single_eq_of_ne hw, Pi.zero_apply]

include hg hf in
theorem Data.SphericalPELAlbaneseData.framedIntegralTateImage_eq_pi :
    Rational.framedIntegralTateImage frame =
      Submodule.pi Set.univ (D.framedSourceLattice T P frame) := by
  classical
  apply le_antisymm
  · intro z hz v _
    exact ⟨z, hz, rfl⟩
  · intro z hz
    rw [← Finset.univ_sum_single z]
    exact Submodule.sum_mem _ fun v _ =>
      D.framedSourceLattice_single_mem hg T P frame hf v (z v) (hz v (Set.mem_univ v))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
