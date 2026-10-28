import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OrdinaryRestriction
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteFlatNeighborhood

/-! # Reduction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Reduction.Construction

noncomputable section

/-! The topological and relative-geometric reduction of Openness to the p-torsion
bound. This file proves the reduction; the bound remains a separate obligation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- Eliminate the dimension witness in the exact ordinary predicate. -/
theorem isOrdinaryAt_iff_torsionPointCard_eq (p : ℕ) (s : S) :
    DefinitionsTorsion.IsOrdinaryAt p A s ↔
      Nat.card {x : DefinitionsTorsion.geometricPoint S s ⟶ A // x ^ p = 1} = p ^ FiberDimension.Construction.fiberDimension A s := by
  constructor
  · rintro ⟨g, hg, hcard⟩
    have hdim : g = FiberDimension.Construction.fiberDimension A s := by
      have h := hg.symm.trans (FiberDimension.Construction.fiberDimension_spec A s)
      exact_mod_cast h
    exact hdim ▸ hcard
  · intro hcard
    exact ⟨FiberDimension.Construction.fiberDimension A s, FiberDimension.Construction.fiberDimension_spec A s, hcard⟩

/-- For a finite torsion kernel, semicontinuity and the p-rank upper bound
give openness of the ordinary locus. -/
theorem isOpen_ordinaryLocus_of_finite_torsion_of_bound
    (p : ℕ) [IsFinite (DefinitionsTorsion.Construction.torsionScheme A p).hom]
    (hbound : ∀ s : S, Nat.card {x : DefinitionsTorsion.geometricPoint S s ⟶ A // x ^ p = 1} ≤
      p ^ FiberDimension.Construction.fiberDimension A s) :
    IsOpen {s : S | DefinitionsTorsion.IsOrdinaryAt p A s} := by
  simp only [isOrdinaryAt_iff_torsionPointCard_eq]
  exact CountTopology.Construction.isOpen_maximalCount_of_lowerSemicontinuous _ _
    (FiniteFlatNeighborhood.Construction.lowerSemicontinuous_torsionPointCard_of_isFinite A p)
    ((FiberDimension.Construction.isLocallyConstant_fiberDimension A).comp (fun n : ℕ => p ^ n)) hbound

/-- Local finiteness near ordinary points suffices for the same reduction.
No global finiteness of the torsion kernel is assumed here. -/
theorem isOpen_ordinaryLocus_of_torsionPointCard_bound
    (p : ℕ) [Fact p.Prime]
    (hbound : ∀ s : S, Nat.card {x : DefinitionsTorsion.geometricPoint S s ⟶ A // x ^ p = 1} ≤
      p ^ FiberDimension.Construction.fiberDimension A s) :
    IsOpen {s : S | DefinitionsTorsion.IsOrdinaryAt p A s} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro s hs
  obtain ⟨U, hsU, hfin⟩ := DefinitionsTorsion.Construction.exists_finite_torsion_neighborhood s A p hs
  have : IsFinite ((DefinitionsTorsion.Construction.torsionScheme A p).hom ∣_ U) := hfin
  let B := (Over.pullback U.ι).obj A
  have : Smooth B.hom := by change Smooth (CategoryTheory.Limits.pullback.snd A.hom U.ι); infer_instance
  have : IsProper B.hom := by change IsProper (CategoryTheory.Limits.pullback.snd A.hom U.ι); infer_instance
  have : GeometricallyConnected B.hom := by
    change GeometricallyConnected (CategoryTheory.Limits.pullback.snd A.hom U.ι)
    infer_instance
  have : IsFinite (DefinitionsTorsion.Construction.torsionScheme B p).hom := BaseChange.Construction.isFinite_torsion_openRestriction A p U
  have hboundB (t : U) : Nat.card {x : DefinitionsTorsion.geometricPoint U t ⟶ B // x ^ p = 1} ≤
      p ^ FiberDimension.Construction.fiberDimension B t := by
    have hdim : FiberDimension.Construction.fiberDimension B t = FiberDimension.Construction.fiberDimension A (U.ι t) := by
      have h := OrdinaryRestriction.Construction.topologicalKrullDim_fiber_openBaseChange U.ι A t
      change topologicalKrullDim (B.hom.fiber t) = _ at h
      have heq := (FiberDimension.Construction.fiberDimension_spec B t).symm.trans
        (h.trans (FiberDimension.Construction.fiberDimension_spec A (U.ι t)))
      exact_mod_cast heq
    exact (OpenBaseChange.Construction.torsionPointCard_openBaseChange U.ι A p t).trans_le
      ((hbound (U.ι t)).trans_eq (congrArg (fun d : ℕ => p ^ d) hdim.symm))
  have hopen := isOpen_ordinaryLocus_of_finite_torsion_of_bound B p hboundB
  refine ⟨U.ι '' {t : U | DefinitionsTorsion.IsOrdinaryAt p B t}, ?_, U.ι.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact (OrdinaryRestriction.Construction.isOrdinaryAt_openBaseChange_iff U.ι A p t).mp ht
  · exact ⟨⟨s, hsU⟩, (OrdinaryRestriction.Construction.isOrdinaryAt_openBaseChange_iff U.ι A p ⟨s, hsU⟩).mpr hs, rfl⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Reduction.Construction
