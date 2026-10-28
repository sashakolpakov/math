import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmpleFiberEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ReducedClosedIs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Ample Closed Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmpleClosedIs.Construction.AmpleClosed

noncomputable section

/-! Proper subschemes contained in an open trivializing an ample bundle are finite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem finite_points {K : Type u} [Field K]
    (Y A : Over (Spec (.of K))) [IsProper Y.hom]
    [LocallyOfFiniteType A.hom] [IsSeparated A.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple) (W : A.left.Opens)
    (e : (L.pullback W.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme)
    (f : Y ⟶ A) (hf : Function.Injective f.left) (hW : Set.range f.left ⊆ W) :
    Finite Y.left := by
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  have hcomp (Z : Set Y.left) (hZ : Z ∈ irreducibleComponents Y.left) : Z.Finite := by
    let C : TopologicalSpace.Closeds Y.left := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
    let I := Scheme.IdealSheafData.vanishingIdeal C
    let T : Over (Spec (.of K)) := Over.mk (I.subschemeι ≫ Y.hom)
    have : IsProper T.hom := by dsimp [T]; infer_instance
    have : IsReduced T.left := ReducedClosedIs.Construction.ReducedClosed.isReduced C
    have : IrreducibleSpace T.left := ReducedClosedIs.Construction.ReducedClosed.irreducibleSpace C hZ.1
    let a : T ⟶ A := Over.homMk (I.subschemeι ≫ f.left) (by simp [T])
    have ha : Set.range a.left ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hW ⟨I.subschemeι x, rfl⟩
    let g := IsOpenImmersion.lift W.ι a.left ha
    have hg : g ≫ W.ι = a.left := IsOpenImmersion.lift_fac W.ι a.left ha
    apply Set.Subsingleton.finite
    intro x hx y hy
    have hr : Set.range I.subschemeι = Z := ReducedClosedIs.Construction.ReducedClosed.range_ι C
    obtain ⟨x', hx'⟩ := hr.symm ▸ hx
    obtain ⟨y', hy'⟩ := hr.symm ▸ hy
    have he := AmpleFiberEq.Construction.AmpleFiber.apply_eq T A L hL W e a g hg x' y'
    apply hf
    rw [← hx', ← hy']
    exact he
  have hfin : (⋃₀ irreducibleComponents Y.left).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sUnion hcomp
  rw [sUnion_irreducibleComponents] at hfin
  exact Set.finite_univ_iff.mp hfin

theorem isFinite {K : Type u} [Field K]
    (Y A : Over (Spec (.of K))) [IsProper Y.hom]
    [LocallyOfFiniteType A.hom] [IsSeparated A.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (hL : L.IsAmple) (W : A.left.Opens)
    (e : (L.pullback W.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule W.toScheme)
    (f : Y ⟶ A) (hf : Function.Injective f.left) (hW : Set.range f.left ⊆ W) :
    IsFinite Y.hom := by
  have : Finite Y.left := finite_points Y A L hL W e f hf hW
  have : LocallyQuasiFinite Y.hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite Y.hom

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmpleClosedIs.Construction.AmpleClosed
