import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorRestriction
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Line Bundle On -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction

noncomputable section

/-! Finite affine covers on which a given line bundle is trivial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} (M : X.Modules)

theorem exists_affine_lineBundle_chart (hM : LineBundle.Construction.IsLineBundle M) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ LineBundle.Construction.structureSheafModule U.toScheme) := by
  obtain ⟨V, hx, ⟨e⟩⟩ := hM x
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hx
  exact ⟨U, hU, hxU, ⟨TensorRestriction.Construction.restrictLineBundleTrivialization hUV e⟩⟩

structure LineBundleAffineCover where
  index : Type u
  [finiteIndex : Fintype index]
  opens : index → X.Opens
  cover : iSup opens = ⊤
  affine : ∀ i, IsAffineOpen (opens i)
  trivialization : ∀ i, (Scheme.Modules.pullback (opens i).ι).obj M ≅
    LineBundle.Construction.structureSheafModule (opens i).toScheme

attribute [instance] LineBundleAffineCover.finiteIndex

theorem exists_lineBundleAffineCover [CompactSpace X] (hM : LineBundle.Construction.IsLineBundle M) :
    Nonempty (LineBundleAffineCover M) := by
  classical
  choose U hU hx he using exists_affine_lineBundle_chart M hM
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨{
    index := t
    opens := fun i ↦ U i.val
    affine := fun i ↦ hU i.val
    trivialization := fun i ↦ (he i.val).some
    cover := ?_ }⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hit, hxi⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨⟨i, hit⟩, hxi⟩

def LineBundleAffineCover.trivializationOn {M : X.Modules} (U : LineBundleAffineCover M)
    (i : U.index) (V : X.Opens) (hV : V ≤ U.opens i) :
    (Scheme.Modules.pullback V.ι).obj M ≅ LineBundle.Construction.structureSheafModule V.toScheme :=
  TensorRestriction.Construction.restrictLineBundleTrivialization hV (U.trivialization i)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleOn.Construction
