import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.CupRefinement

/-! # Refinement Operations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.RefinementOperations

noncomputable section

/-! Composition and finite-sum formulas for the actual restriction
maps used in Cech refinement. A boundary after refinement gives zero
original native H2 class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped BigOperators

theorem commonOpenCover_covers {T I J : Type*} [TopologicalSpace T]
    (U : I → Opens T) (V : J → Opens T) (hU : iSup U = ⊤) (hV : iSup V = ⊤) :
    iSup (fun p : I × J => U p.1 ⊓ V p.2) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ iSup U := by rw [hU]; trivial
  have hy : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hy
  exact Opens.mem_iSup.mpr ⟨⟨i, j⟩, hi, hj⟩

variable (X : Scheme.{0}) {I J K : Type}
    (U : I → X.Opens) (V : J → X.Opens) (W : K → X.Opens)
    (r : J → I) (s : K → J) (hr : ∀ j, V j ≤ U (r j)) (hs : ∀ k, W k ≤ V (s k))

theorem regularPairRefinement_comp (v : ∀ i j, Γ(X, U i ⊓ U j)) :
    RegularPair.Refinement.regularPairRefinement X V W s hs (RegularPair.Refinement.regularPairRefinement X U V r hr v) =
      RegularPair.Refinement.regularPairRefinement X U W (r ∘ s) (fun k => (hs k).trans (hr (s k))) v := by
  funext i j
  dsimp only [RegularPair.Refinement.regularPairRefinement, Function.comp_apply]
  rw [RegularPair.Closed.regularSectionRestrict_comp]

theorem regularTripleRefinement_add
    (v w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l)) :
    CupRefinement.regularTripleRefinement X U V r hr (fun i j l => v i j l + w i j l) =
      fun i j l => CupRefinement.regularTripleRefinement X U V r hr v i j l +
        CupRefinement.regularTripleRefinement X U V r hr w i j l := by
  funext i j l
  exact map_add _ _ _

theorem regularTripleRefinement_sum {B : Type} (t : Finset B)
    (w : B → ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l)) :
    CupRefinement.regularTripleRefinement X U V r hr (fun i j l => ∑ a ∈ t, w a i j l) =
      fun i j l => ∑ a ∈ t, CupRefinement.regularTripleRefinement X U V r hr (w a) i j l := by
  funext i j l
  exact map_sum _ _ _

theorem regularTripleSheafClass_zero_of_refinement_boundary
    (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (w : ∀ i j l, Γ(X, (U i ⊓ U j) ⊓ U l))
    (hw : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj U 2
      (BoundaryShuffle.regularTripleCechCochain X U w) = 0)
    (p : ∀ i j, Γ(X, V i ⊓ V j))
    (hp : BoundaryShuffle.RegularTripleBoundary X V p (CupRefinement.regularTripleRefinement X U V r hr w)) :
    DivisorClass.Chern.Abelian.CechClasses.abelianCechSheafClass U (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf) hU 1
      (BoundaryShuffle.regularTripleCechCochain X U w) hw =
      (0 : (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X.toPresheafedSpace.carrier) 2).obj (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf)) :=
  (CupRefinement.regularTripleSheafClass_refinement X U V r hr hU hV w hw).symm.trans
    (BoundaryShuffle.regularTripleCechClass_eq_zero X V hV p _ hp)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.RefinementOperations
