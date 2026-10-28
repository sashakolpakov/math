import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricOppositeLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricWeilIntegralFrame
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScalarLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.DualScalarLattices

/-! # Central Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual central IsogenyQuotient isogeny's lattice is exactly the lattice
of multiplication by q, on both chosen and opposite blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj Pointwise

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hgeometry : D.HasIntegralModelGeometry) (hIsogenyQuotient : D.RealizesIsogenyQuotient) (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
  {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)
  (frame : D.FiberFrame b x)
  (hf : Rational.IsSplitActionFrame (D.fiberFamily b x) (Over.mk (𝟙 (Spec (.of k)))) q D.localCharacter frame)
  (c : (D.correspondence (Local.IntegralType.central s)).Fiber x)

include hg hgeometry hf hElementaryDivisors in
omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.centralChosenTateLattice (v : Fin s) :
    Rational.framedTateLattice frame
      (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x
        (c.val ≫ (D.correspondence (Local.IntegralType.central s)).target) c.val c.property rfl).isogeny.hom (v, false) =
      (HeckeKernel.qUnit q)⁻¹ • (D.framedFiberSourceLattice b x frame (v, false)).val := by
  obtain ⟨M, hM, hpos⟩ := D.c46Fiber_projectedRelativePosition b x frame hg hgeometry hIsogenyQuotient
    (Local.IntegralType.central s) (c.val ≫ (D.correspondence (Local.IntegralType.central s)).target)
    c.val c.property rfl hf hElementaryDivisors v
  exact hM.symm.trans (ScalarLattices.relativePosition_scalar q _ M hpos)

include hg hgeometry hf hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralOppositeTateLattice (v : Fin s) :
    Rational.framedTateLattice frame
      (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x
        (c.val ≫ (D.correspondence (Local.IntegralType.central s)).target) c.val c.property rfl).isogeny.hom (v, true) =
      (HeckeKernel.qUnit q)⁻¹ • (D.framedFiberSourceLattice b x frame (v, true)).val := by
  have he := D.geometricIsogeny_opposite_lattice hg hgeometry frame hf
    (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x
      (c.val ≫ (D.correspondence (Local.IntegralType.central s)).target) c.val c.property rfl) v
  rw [D.centralChosenTateLattice hg hgeometry hIsogenyQuotient hElementaryDivisors b x frame hf c v,
    DualScalarLattices.dualSubmodule_unit_smul, inv_inv, ← mul_smul,
    ← D.geometricWeilSource_opposite hg hgeometry b x frame hf v] at he
  have hu : ((HeckeKernel.qUnit q) ^ (Local.IntegralType.central s).multiplierNat)⁻¹ * HeckeKernel.qUnit q = (HeckeKernel.qUnit q)⁻¹ := by
    change ((HeckeKernel.qUnit q) ^ 2)⁻¹ * HeckeKernel.qUnit q = (HeckeKernel.qUnit q)⁻¹
    group
  rw [hu] at he
  exact he

omit [CharZero k] in
theorem Data.SphericalPELAlbaneseData.multiplicationFramedTateLattice (v : Fin s × Bool) :
    Rational.framedTateLattice frame ((𝟙 (D.fiberFamily b x).abelian.scheme) ^ q) v =
      (HeckeKernel.qUnit q)⁻¹ • (D.framedFiberSourceLattice b x frame v).val := by
  unfold Rational.framedTateLattice
  rw [ScalarLattices.multiplicationTatePreimage, ScalarLattices.latticeMap_unit_smul frame.toLinearMap]
  exact ScalarLattices.latticeMap_unit_smul
    (LinearMap.proj v : Rational.SplitTateSpace s q →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q]))
    (Rational.framedIntegralTateImage frame) ((HeckeKernel.qUnit q)⁻¹)

include hg hgeometry hf hElementaryDivisors in
theorem Data.SphericalPELAlbaneseData.centralTatePreimage_eq_multiplication :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
      (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x
        (c.val ≫ (D.correspondence (Local.IntegralType.central s)).target) c.val c.property rfl).isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q)
        ((𝟙 (D.fiberFamily b x).abelian.scheme) ^ q) := by
  apply Submodule.map_injective_of_injective (f := frame.toLinearMap.restrictScalars ℤ_[q]) frame.injective
  rw [D.framedTatePreimage_eq_pi hg _ frame hf D.reference.polarizationType
    (D.fiberPolarizationType hgeometry b x) hg.2.2.2.2,
    ScalarLattices.multiplicationTatePreimage, ScalarLattices.latticeMap_unit_smul frame.toLinearMap]
  change Submodule.pi Set.univ _ = (HeckeKernel.qUnit q)⁻¹ • Rational.framedIntegralTateImage frame
  rw [D.framedIntegralTateImage_eq_pi hg _ (D.fiberFamily b x) frame hf]
  have hblocks : Rational.framedTateLattice frame
      (D.c46FiberIsogeny hIsogenyQuotient (Local.IntegralType.central s) x
        (c.val ≫ (D.correspondence (Local.IntegralType.central s)).target) c.val c.property rfl).isogeny.hom =
      fun v => (HeckeKernel.qUnit q)⁻¹ • D.framedSourceLattice _ (D.fiberFamily b x) frame v := by
    funext v
    obtain ⟨v, side⟩ := v
    cases side
    · exact D.centralChosenTateLattice hg hgeometry hIsogenyQuotient hElementaryDivisors b x frame hf c v
    · exact D.centralOppositeTateLattice hg hgeometry hIsogenyQuotient hElementaryDivisors b x frame hf c v
  rw [hblocks]
  ext z
  change (∀ v, v ∈ Set.univ → z v ∈ (HeckeKernel.qUnit q)⁻¹ • (D.framedSourceLattice _ (D.fiberFamily b x) frame v : Set _)) ↔
    z ∈ (HeckeKernel.qUnit q)⁻¹ • (Submodule.pi Set.univ (D.framedSourceLattice _ (D.fiberFamily b x) frame) : Set _)
  simp only [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
