import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricBranches
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SingletonEtaleFibers

/-! # Central Branches -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The central correspondence has exactly one actual branch over each
geometric source point. This follows from the geometric raw-coset
bijection and centrality of the scalar local representative. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem CentralBranches.rawScalarBlock_card (q : ℕ) [Fact q.Prime] (a : ℤ) :
    Nat.card (IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
      (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun _ => a))) = 1 := by
  have he : IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun _ => a) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (HeckeKernel.qUnit q ^ a) := by
    apply Units.ext
    rfl
  have hc (g : Matrix.GeneralLinearGroup (Fin 3) ℚ_[q]) :
      Commute g (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun _ => a)) := by
    rw [he]
    exact (Matrix.GeneralLinearGroup.scalar_commute (HeckeKernel.qUnit q ^ a) g).symm
  change Nat.card {x // x ∈ HeckeKernel.doubleCosetOrbit (IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q)
    (IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (fun _ => a))} = 1
  rw [CentralConvolution.doubleCosetOrbit_central _ _ hc]
  simp

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
  (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s) (h : D.HasIntegralModelGeometry)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) {k : Type} [Field k] [IsAlgClosed k]
  (b : Spec (.of k) ⟶ Spec (.of K)) (x : D.GeometricPoint b)

include hg hdegree hs h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.centralBranchCount : Nat.card ((D.correspondence (Local.IntegralType.central s)).Fiber x) = 1 := by
  rw [D.geometricBranchCount hg hdegree hs h b x hIsogenyQuotient]
  simp only [Local.IntegralType.exponentNat, Local.IntegralType.central, Local.LocalType.central, Int.toNat_one,
    Nat.cast_one, CentralBranches.rawScalarBlock_card, Finset.prod_const_one]

include hg hdegree hs h hIsogenyQuotient in
theorem Data.SphericalPELAlbaneseData.centralSource_isIso : IsIso (D.correspondence (Local.IntegralType.central s)).source :=
  (D.correspondence (Local.IntegralType.central s)).source_isIso_of_fiber_card_one
    (fun k _ _ b x => D.centralBranchCount hg hdegree hs h hIsogenyQuotient (k := k) b x)

def Data.SphericalPELAlbaneseData.centralSourceIso : (D.correspondence (Local.IntegralType.central s)).cover ≅ D.space := by
  have := D.centralSource_isIso hg hdegree hs h hIsogenyQuotient
  exact asIso (D.correspondence (Local.IntegralType.central s)).source

def Data.SphericalPELAlbaneseData.centralTargetMap : D.space ⟶ D.space :=
  (D.centralSourceIso hg hdegree hs h hIsogenyQuotient).inv ≫
    (D.correspondence (Local.IntegralType.central s)).target

theorem Data.SphericalPELAlbaneseData.centralTargetMap_factor :
    (D.correspondence (Local.IntegralType.central s)).source ≫ D.centralTargetMap hg hdegree hs h hIsogenyQuotient =
      (D.correspondence (Local.IntegralType.central s)).target := by
  change (D.centralSourceIso hg hdegree hs h hIsogenyQuotient).hom ≫
    (D.centralSourceIso hg hdegree hs h hIsogenyQuotient).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

theorem Data.SphericalPELAlbaneseData.central_neighbors :
    D.neighbors (Local.IntegralType.central s) b x = {x ≫ D.centralTargetMap hg hdegree hs h hIsogenyQuotient} := by
  have := D.centralSource_isIso hg hdegree hs h hIsogenyQuotient
  exact (D.correspondence (Local.IntegralType.central s)).neighbors_of_source_iso b x

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
