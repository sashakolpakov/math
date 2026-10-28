import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.LocalTrace
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.OverCoproduct
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Trace Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Effective descent constructs the algebraic trace of a finite etale
correspondence into a separated commutative group scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {B : Scheme.{0}} {X A : Over B} [GrpObj A] [IsCommMonObj A]
  [IsReduced X.left] [IsLocallyNoetherian X.left] [IsSeparated A.hom]
  (C : Correspondences.EtaleCorrespondence X) (f : X ⟶ A)

/-- The actual algebraic trace exists and is uniquely determined by
the sum over the geometric source fiber. Its construction uses proved
overlap compatibility and effective descent, with no trace-map input. -/
theorem Correspondences.EtaleCorrespondence.exists_algebraicTrace :
    ∃! τ : X ⟶ A, ∀ (k : Type) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X),
      x ≫ τ = C.geometricTrace f b x := by
  let Y : Over X.left := Over.mk C.source.left
  have : IsFinite Y.hom := C.finite
  have : Etale Y.hom := C.etale
  let cover := AbelianModuli.ReferenceFamily.SchemeSplitting.EtaleSplitting.finiteEtaleSplitCover Y
  let U : cover.Index → Over B := fun i => Over.mk (cover.map i ≫ X.hom)
  let p : ∀ i, U i ⟶ X := fun i => Over.homMk (cover.map i) rfl
  let e : ∀ i, C.BranchSplitting (p i) (cover.rank i) :=
    fun i => TateComparison.BranchSplitting.constantCoproductIso (cover.source i) (Fin (cover.rank i)) ≪≫ cover.presentation i
  let v : ∀ i, U i ⟶ A := fun i => C.localTraceMap f (p i) (e i)
  let P := OverCoproduct.overCoproduct U
  let π : P ⟶ X := OverCoproduct.overCoproductDesc U p
  let ν : P ⟶ A := OverCoproduct.overCoproductDesc U v
  have hπEtale : Etale π.left := cover.projection_etale
  have hπSurjective : Surjective π.left := cover.projection_surjective
  have hν : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ B) (z : Over.mk b ⟶ P),
      z ≫ ν = C.geometricTrace f b (z ≫ π) := by
    intro k _ _ b z
    obtain ⟨i, zi, hzi⟩ := OverCoproduct.overCoproduct_point_factor U b z
    change z ≫ OverCoproduct.overCoproductDesc U v = C.geometricTrace f b (z ≫ OverCoproduct.overCoproductDesc U p)
    rw [← hzi]
    simp only [Category.assoc, OverCoproduct.overCoproductι_desc]
    exact C.localTraceMap_geometric f (p i) (e i) b zi
  have : IsReduced P.left := TateComparison.Etale.etale_source_reduced π.left
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian π.left
  let R : Over B := Over.mk (pullback.fst π.left π.left ≫ P.hom)
  have : IsReduced R.left := TateComparison.Etale.etale_source_reduced (pullback.fst π.left π.left)
  let r₁ : R ⟶ P := Over.homMk (pullback.fst π.left π.left) rfl
  let r₂ : R ⟶ P := Over.homMk (pullback.snd π.left π.left) (by
    change pullback.snd π.left π.left ≫ P.hom = pullback.fst π.left π.left ≫ P.hom
    rw [← π.w, ← Category.assoc, ← Category.assoc, pullback.condition])
  have hr : r₁ ≫ π = r₂ ≫ π := Over.OverMorphism.ext pullback.condition
  have hc : r₁ ≫ ν = r₂ ≫ ν := by
    apply GeometricExt.over_hom_ext_geometric
    intro k _ _ b z
    rw [← Category.assoc, ← Category.assoc, hν, hν, Category.assoc, Category.assoc, hr]
  have hpair : pullback.fst π.left π.left ≫ ν.left = pullback.snd π.left π.left ≫ ν.left :=
    congrArg (fun z => z.left) hc
  have hcoeq : ∀ {W : Scheme} (a b : W ⟶ P.left), a ≫ π.left = b ≫ π.left →
      a ≫ ν.left = b ≫ ν.left := by
    intro W a b hab
    let l := pullback.lift a b hab
    have hl := congrArg (fun z => l ≫ z) hpair
    simpa only [l, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using hl
  let τ₀ := EffectiveEpi.desc π.left ν.left hcoeq
  have hτ₀ : π.left ≫ τ₀ = ν.left := EffectiveEpi.fac _ _ _
  have hbase : τ₀ ≫ A.hom = X.hom := by
    apply (cancel_epi π.left).mp
    rw [← Category.assoc, hτ₀, ν.w, π.w]
  let τ : X ⟶ A := Over.homMk τ₀ hbase
  have hτ : π ≫ τ = ν := Over.OverMorphism.ext hτ₀
  have hpoints : ∀ (k : Type) [Field k] [IsAlgClosed k]
      (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X), x ≫ τ = C.geometricTrace f b x := by
    intro k _ _ b x
    obtain ⟨z, hz⟩ := TateComparison.Etale.etale_surjective_geometric_lift π b x
    rw [← hz, Category.assoc, hτ, hν]
  refine ⟨τ, hpoints, ?_⟩
  intro τ' hτ'
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  exact (hτ' k b x).trans (hpoints k b x).symm

def Correspondences.EtaleCorrespondence.algebraicTrace : X ⟶ A := (C.exists_algebraicTrace f).choose

theorem Correspondences.EtaleCorrespondence.algebraicTrace_geometric {k : Type} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ B) (x : Over.mk b ⟶ X) :
    x ≫ C.algebraicTrace f = C.geometricTrace f b x :=
  (C.exists_algebraicTrace f).choose_spec.1 k b x

theorem Correspondences.EtaleCorrespondence.algebraicTrace_local_reduced {T : Over B} [IsReduced T.left]
    (x : T ⟶ X) {n : ℕ} (e : C.BranchSplitting x n) :
    x ≫ C.algebraicTrace f = C.localTraceMap f x e := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b a
  rw [← Category.assoc, Correspondences.EtaleCorrespondence.algebraicTrace_geometric, Correspondences.EtaleCorrespondence.localTraceMap_geometric]

/-- The descended trace respects chronological composition of the actual
finite-etale correspondences, with all branch multiplicities. -/
theorem Correspondences.EtaleCorrespondence.algebraicTrace_comp (D : Correspondences.EtaleCorrespondence X) :
    (C.comp D).algebraicTrace f = C.algebraicTrace (D.algebraicTrace f) := by
  apply GeometricExt.over_hom_ext_geometric
  intro k _ _ b x
  rw [Correspondences.EtaleCorrespondence.algebraicTrace_geometric, Correspondences.EtaleCorrespondence.algebraicTrace_geometric]
  simp only [Correspondences.EtaleCorrespondence.geometricTrace, Correspondences.EtaleCorrespondence.neighbors_comp, Multiset.map_bind, Multiset.prod_bind,
    Correspondences.EtaleCorrespondence.algebraicTrace_geometric]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
