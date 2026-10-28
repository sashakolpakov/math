import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedBlockLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition

/-! # Framed Lattice Quotients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual Tate-block cokernel is the quotient of the two projected
lattices used by the geometric flag statement. -/

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

theorem Data.SphericalPELAlbaneseData.framedTargetBlockMap_comp (v : Fin s × Bool) :
    (D.framedTargetBlockMap h e frame v).comp (D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v) =
      D.framedSourceBlockMap h (Over.mk (𝟙 (Spec (.of k)))) P frame v := by
  apply LinearMap.ext
  intro x
  funext i
  exact congrArg (fun z => frame z v i)
    (PreimageQuotient.targetTatePreimageEquiv_map (𝟙 (Spec (.of k))) q e.isogeny x.val)

include h hf δ hδ hq in
theorem Data.SphericalPELAlbaneseData.framedSourceLattice_le_target (v : Fin s × Bool) :
    D.framedSourceLattice (Over.mk (𝟙 (Spec (.of k)))) P frame v ≤
      Rational.framedTateLattice frame e.isogeny.hom v := by
  rw [← D.framedSourceBlockMap_range h (Over.mk (𝟙 (Spec (.of k)))) P frame hf v,
    ← D.framedTargetBlockMap_range h e frame hf δ hδ hq v]
  rintro z ⟨x, rfl⟩
  exact ⟨D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v x,
    congrArg (fun f => f x) (D.framedTargetBlockMap_comp h e frame v)⟩

def Data.SphericalPELAlbaneseData.framedTargetBlockEquiv (v : Fin s × Bool) :
    D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v ≃ₗ[ℤ_[q]]
      Rational.framedTateLattice frame e.isogeny.hom v :=
  (LinearEquiv.ofInjective (D.framedTargetBlockMap h e frame v)
    (D.framedTargetBlockMap_injective h e frame hf δ hδ hq v)).trans
      (LinearEquiv.ofEq _ _ (D.framedTargetBlockMap_range h e frame hf δ hδ hq v))

theorem Data.SphericalPELAlbaneseData.framedTargetBlockEquiv_coe (v : Fin s × Bool)
    (y : D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v) :
    (D.framedTargetBlockEquiv h e frame hf δ hδ hq v y).val = D.framedTargetBlockMap h e frame v y := by
  simp only [Data.SphericalPELAlbaneseData.framedTargetBlockEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]

def Data.SphericalPELAlbaneseData.sourceInFramedTateLattice (v : Fin s × Bool) :
    Submodule ℤ_[q] (Rational.framedTateLattice frame e.isogeny.hom v) :=
  (D.framedSourceLattice (Over.mk (𝟙 (Spec (.of k)))) P frame v).comap
    (Rational.framedTateLattice frame e.isogeny.hom v).subtype

theorem Data.SphericalPELAlbaneseData.framedTargetBlockEquiv_range (v : Fin s × Bool) :
    (D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v).range.map
      (D.framedTargetBlockEquiv h e frame hf δ hδ hq v).toLinearMap =
        D.sourceInFramedTateLattice e frame v := by
  ext z
  change z ∈ _ ↔ z.val ∈ D.framedSourceLattice (Over.mk (𝟙 (Spec (.of k)))) P frame v
  rw [← D.framedSourceBlockMap_range h (Over.mk (𝟙 (Spec (.of k)))) P frame hf v]
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    rw [LinearEquiv.coe_coe, D.framedTargetBlockEquiv_coe h e frame hf δ hδ hq v]
    exact (congrArg (fun f => f x) (D.framedTargetBlockMap_comp h e frame v)).symm
  · rintro ⟨x, hx⟩
    refine ⟨D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v x, ⟨x, rfl⟩, ?_⟩
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, D.framedTargetBlockEquiv_coe h e frame hf δ hδ hq v]
    exact (congrArg (fun f => f x) (D.framedTargetBlockMap_comp h e frame v)).trans hx

abbrev Data.SphericalPELAlbaneseData.framedTateLatticeQuotient (v : Fin s × Bool) :=
  Rational.framedTateLattice frame e.isogeny.hom v ⧸ D.sourceInFramedTateLattice e frame v

def Data.SphericalPELAlbaneseData.tateBlockCokernelEquivFramedQuotient (v : Fin s × Bool) :
    (D.integralTateBlock h (Over.mk (𝟙 (Spec (.of k)))) Q v ⧸
      (D.tateBlockMap h (Over.mk (𝟙 (Spec (.of k)))) e v).range) ≃ₗ[ℤ_[q]]
      D.framedTateLatticeQuotient e frame v :=
  Submodule.Quotient.equiv _ _ (D.framedTargetBlockEquiv h e frame hf δ hδ hq v)
    (D.framedTargetBlockEquiv_range h e frame hf δ hδ hq v)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
