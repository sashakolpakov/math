import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BranchBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceDescent
import Mathlib.AlgebraicGeometry.Sites.Etale

/-! # Trace All Tests -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceAllTests

noncomputable section

/-! The descended algebraic trace has its branch-sum formula on every
test scheme, including nonreduced affine tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

local instance : Scheme.JointlySurjective
    (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
  Scheme.instJointlySurjectivePrecoverage

local instance : Scheme.IsJointlySurjectivePreserving (@Etale : MorphismProperty Scheme.{0}) :=
  Scheme.isJointlySurjectivePreserving _

local instance : (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})).IsStableUnderBaseChange :=
  Scheme.instIsStableUnderBaseChangePrecoverageOfIsJointlySurjectivePreservingOfIsStableUnderBaseChange _

theorem etaleCover_hom_ext {X Y : Scheme.{0}}
    (U : X.Cover.{0} (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0}))) (f g : X ⟶ Y)
    (h : ∀ i, U.f i ≫ f = U.f i ≫ g) : f = g := by
  let p : (∐ U.X) ⟶ X := Sigma.desc U.f
  have : Etale p := by
    have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := @RingHom.Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) U.map_prop
  have : Surjective p := by
    constructor
    intro x
    obtain ⟨i, z, hz⟩ := U.exists_eq x
    refine ⟨Sigma.ι U.X i z, ?_⟩
    exact (congrArg (fun f : U.X i ⟶ X => f z) (Sigma.ι_comp_desc U.f i)).trans hz
  apply (cancel_epi p).mp
  apply Sigma.hom_ext
  intro i
  exact (Sigma.ι_comp_desc_assoc U.f i f).trans ((h i).trans (Sigma.ι_comp_desc_assoc U.f i g).symm)

namespace EtaleCorrespondence

variable {B : Scheme.{0}} {X A : Over B} [GrpObj A] [IsCommMonObj A]
  [IsReduced X.left] [IsLocallyNoetherian X.left] [IsSeparated A.hom]
  (C : Correspondences.EtaleCorrespondence X) (f : X ⟶ A)

/-- The constructed global trace agrees with the actual sum of branches
after every base change. Reducedness is required only of the original
source used to construct the global morphism. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence.algebraicTrace_local {T : Over B}
    (x : T ⟶ X) {n : ℕ} (e : C.BranchSplitting x n) :
    x ≫ C.algebraicTrace f = C.localTraceMap f x e := by
  let Y : Over X.left := Over.mk C.source.left
  have : IsFinite Y.hom := C.finite
  have : Etale Y.hom := C.etale
  let cover := AbelianModuli.ReferenceFamily.SchemeSplitting.EtaleSplitting.finiteEtaleSplitCover Y
  let cv : X.left.Cover.{0} (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
    .mkOfCovers cover.Index cover.source cover.map cover.covers cover.etale
  apply Over.OverMorphism.ext
  apply etaleCover_hom_ext (cv.pullback₂ x.left)
  intro i
  let U : Over B := Over.mk (cover.map i ≫ X.hom)
  let p : U ⟶ X := Over.homMk (cover.map i) rfl
  let ei : C.BranchSplitting p (cover.rank i) :=
    TateComparison.BranchSplitting.constantCoproductIso (cover.source i) (Fin (cover.rank i)) ≪≫ cover.presentation i
  have : Etale p.left := cover.etale i
  have : IsReduced U.left := TateComparison.Etale.etale_source_reduced p.left
  let W : Over B := Over.mk (pullback.snd (cover.map i) x.left ≫ T.hom)
  let j : W ⟶ T := Over.homMk (pullback.snd (cover.map i) x.left) rfl
  let a : W ⟶ U := Over.homMk (pullback.fst (cover.map i) x.left) (by
    change pullback.fst (cover.map i) x.left ≫ cover.map i ≫ X.hom =
      pullback.snd (cover.map i) x.left ≫ T.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, x.w])
  have hc : a ≫ p = j ≫ x := Over.OverMorphism.ext pullback.condition
  have h : j ≫ (x ≫ C.algebraicTrace f) = j ≫ C.localTraceMap f x e := by
    rw [← Category.assoc, ← hc, Category.assoc, C.algebraicTrace_local_reduced f p ei]
    exact C.localTraceMap_overlap_all p f x ei e a j hc
  exact congrArg (fun z => z.left) h

end EtaleCorrespondence

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TraceAllTests
