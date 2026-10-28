import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Locus -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

noncomputable section

/-! CMPoints's density on connected components yields an actual dense open
ordinary locus on every component of its geometric source fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem dense_of_dense_on_connected_components
    {X : Type*} [TopologicalSpace X] (U : Set X)
    (h : ∀ x : X, Dense {y : connectedComponent x | y.val ∈ U}) : Dense U := by
  intro x
  have hx := h x ⟨x, mem_connectedComponent⟩
  exact (closure_mono (Set.image_preimage_subset Subtype.val U))
    (mem_closure_image continuous_subtype_val.continuousAt hx)

theorem coproduct_inclusion_open {B : Scheme} {I : Type}
    (X : I → Over B) (i : I) : IsOpenImmersion (Sigma.ι X i).left := by
  let F := Over.forget B
  let c : (∐ fun j => (X j).left) ⟶ (∐ X).left := sigmaComparison F X
  have : IsIso c := inferInstanceAs (IsIso (sigmaComparison F X))
  have : IsOpenImmersion c := IsOpenImmersion.of_isIso c
  have he : (Sigma.ι X i).left = Sigma.ι (fun j => (X j).left) i ≫ c := by
    exact (ι_comp_sigmaComparison F X i).symm
  rw [he]
  exact IsOpenImmersion.comp (Sigma.ι (fun j => (X j).left) i) c

def componentInclusion {B : Scheme} {T : Over B} {r : ℕ}
    (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T r) (e : (∐ D.S) ≅ T) (i : Fin r) : D.S i ⟶ T :=
  Sigma.ι D.S i ≫ e.hom

theorem componentInclusion_open {B : Scheme} {T : Over B} {r : ℕ}
    (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData T r) (e : (∐ D.S) ≅ T) (i : Fin r) :
    IsOpenImmersion (componentInclusion D e i).left := by
  let : IsOpenImmersion (Sigma.ι D.S i).left := coproduct_inclusion_open D.S i
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget B).map e.hom))
  change IsOpenImmersion ((Sigma.ι D.S i).left ≫ e.hom.left)
  infer_instance

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)

def componentFiber (a : M.Family) (i : Fin (M.componentCount a)) :=
  (Over.pullback R.geometricBase).obj ((M.components a).S i)

def componentFiberInclusion (a : M.Family) (i : Fin (M.componentCount a)) :
    componentFiber R a i ⟶ R.geometricFiber a :=
  (Over.pullback R.geometricBase).map
    (componentInclusion (M.components a) (M.decomposition a) i)

theorem componentFiberInclusion_open (a : M.Family) (i : Fin (M.componentCount a)) :
    IsOpenImmersion (componentFiberInclusion R a i).left :=
  MorphismProperty.overPullbackMap (P := @IsOpenImmersion) R.geometricBase
    (componentInclusion (M.components a) (M.decomposition a) i)
    (componentInclusion_open (M.components a) (M.decomposition a) i)

def componentOrdinaryLocus (a : M.Family) (i : Fin (M.componentCount a)) :
    Set (componentFiber R a i).left :=
  (componentFiberInclusion R a i).left ⁻¹' R.ordinaryLocus a

theorem componentOrdinaryLocus_open_dense (a : M.Family)
    (ho : IsOpen (R.ordinaryLocus a))
    (hd : ∀ x : R.geom a, Dense {y : connectedComponent x | R.IsOrdinary a y.val})
    (i : Fin (M.componentCount a)) :
    IsOpen (componentOrdinaryLocus R a i) ∧ Dense (componentOrdinaryLocus R a i) := by
  let : IsOpenImmersion (componentFiberInclusion R a i).left :=
    componentFiberInclusion_open R a i
  refine ⟨ho.preimage (componentFiberInclusion R a i).left.continuous, ?_⟩
  exact (dense_of_dense_on_connected_components (R.ordinaryLocus a) hd).preimage
    (componentFiberInclusion R a i).left.isOpenEmbedding.isOpenMap

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM
