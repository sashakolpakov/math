import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTowerSubspace
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredHeckeDimensionTransport
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeSubspaceBaseChange

/-! # Tower Filtered Hecke Rank -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TowerFilteredHeckeRank.ScalarTowerComparison

noncomputable section

/-! Filtered generalized eigenspace dimensions agree across genuine scalar towers and compatible embeddings of eigenvalues. -/

open scoped TensorProduct

variable (K A L : Type*) [Field K] [Field A] [Field L]
  [Algebra K A] [Algebra K L] [Algebra A L] [IsScalarTower K A L]
  {V I : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem filtered_hecke_finrank (T : I → Module.End K V) (χ : I → A) (P : Submodule K V) :
    Module.finrank L
        (Linear.generalizedHeckeSummand (fun i => (T i).baseChange L) (fun i => algebraMap A L (χ i)) ⊓
          P.baseChange L : Submodule L (L ⊗[K] V)) =
      Module.finrank A
        (Linear.generalizedHeckeSummand (fun i => (T i).baseChange A) χ ⊓
          P.baseChange A : Submodule A (A ⊗[K] V)) := by
  have h := FilteredHeckeDimensionTransport.GeneralizedHecke.filtered_summand_finrank (ScalarTowerSubspace.ScalarTowerComparison.equiv K A L V)
    (fun i => ((T i).baseChange A).baseChange L) (fun i => (T i).baseChange L)
    (fun i x => LinearMap.congr_fun (ScalarTowerSubspace.ScalarTowerComparison.naturality K A L (T i)) x)
    (fun i => algebraMap A L (χ i)) ((P.baseChange A).baseChange L) (P.baseChange L)
    (ScalarTowerSubspace.ScalarTowerComparison.subspace K A L P)
  exact h.trans (HeckeSubspaceBaseChange.SubspaceBaseChange.filtered_finrank (L := L)
    (fun i => (T i).baseChange A) χ (P.baseChange A))

variable (B : Type*) [Field B] [Algebra K B] [Algebra B L] [IsScalarTower K B L]

theorem compare_filtered_hecke_finrank (T : I → Module.End K V)
    (χA : I → A) (χB : I → B) (hχ : ∀ i, algebraMap A L (χA i) = algebraMap B L (χB i))
    (P : Submodule K V) :
    Module.finrank A
        (Linear.generalizedHeckeSummand (fun i => (T i).baseChange A) χA ⊓
          P.baseChange A : Submodule A (A ⊗[K] V)) =
      Module.finrank B
        (Linear.generalizedHeckeSummand (fun i => (T i).baseChange B) χB ⊓
          P.baseChange B : Submodule B (B ⊗[K] V)) := by
  have ha := filtered_hecke_finrank K A L T χA P
  have hb := filtered_hecke_finrank K B L T χB P
  rw [show (fun i => algebraMap A L (χA i)) = (fun i => algebraMap B L (χB i)) from funext hχ] at ha
  exact ha.symm.trans hb

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TowerFilteredHeckeRank.ScalarTowerComparison
