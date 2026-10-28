import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementFamilyEquality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.CoverRefinementQuasiIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity

/-! # Cover Refinement Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CoverRefinementQuasiIso.Cech

noncomputable section

/-! The original full Čech refinement is a quasi-isomorphism when two
affine families cover the same open subset of a separated scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Z : Scheme.{u}}

theorem image_quasiIso (f : Z ⟶ X) [IsOpenImmersion f] [Z.IsSeparated]
    {ι κ : Type u} (U : ι → Z.Opens) (V : κ → Z.Opens)
    (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (M : X.Modules) [M.IsQuasicoherent]
    (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i)) :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (f.opensFunctor.obj ∘ U)
      (f.opensFunctor.obj ∘ V)
      (Cech.RefinementProductCoordinates.mappedCover f.opensFunctor U V r) M.presheaf) := by
  let : ∀ (n : ℕ) (z : Fin (n + 1) → ι),
      PreservesLimit (Discrete.functor (U ∘ z)) f.opensFunctor := fun n z => by
    change PreservesLimit (Discrete.functor (U ∘ z)) f.isOpenEmbedding.functor
    infer_instance
  let : ∀ (n : ℕ) (z : Fin (n + 1) → κ),
      PreservesLimit (Discrete.functor (V ∘ z)) f.opensFunctor := fun n z => by
    change PreservesLimit (Discrete.functor (V ∘ z)) f.isOpenEmbedding.functor
    infer_instance
  let : QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r
      (f.opensFunctor.op ⋙ M.presheaf)) :=
    Cech.CoverRefinementQuasiIso.quasiIso U V r
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj (M.restrict f)) hU hV
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic (M.restrict f) U haU)
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoverCechAcyclicity.IntrinsicCech.quasicoherent_affine_intersections_acyclic (M.restrict f) V haV)
  exact Cech.RefinementProductCoordinates.quasiIso f.opensFunctor U V r M.presheaf

theorem quasiIso [X.IsSeparated] {ι κ : Type u}
    (U : ι → X.Opens) (V : κ → X.Opens)
    (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
    (M : X.Modules) [M.IsQuasicoherent] (O : X.Opens)
    (hU : iSup U = O) (hV : iSup V = O)
    (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i)) :
    QuasiIso (Cech.CoverRefinement.map U V r M.presheaf) := by
  let : O.toScheme.IsSeparated := ⟨by
    have h : IsSeparated (O.ι ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  let U' : ι → O.toScheme.Opens := fun i => O.ι ⁻¹ᵁ U i
  let V' : κ → O.toScheme.Opens := fun i => O.ι ⁻¹ᵁ V i
  let r' : FormalCoproduct.mk κ V' ⟶ FormalCoproduct.mk ι U' :=
    ⟨r.f, fun i => (Opens.map O.ι.base).map (r.φ i)⟩
  have hU' : iSup U' = ⊤ := by
    dsimp only [U']
    rw [← O.ι.preimage_iSup, hU, O.ι_preimage_self]
  have hV' : iSup V' = ⊤ := by
    dsimp only [V']
    rw [← O.ι.preimage_iSup, hV, O.ι_preimage_self]
  have hUi (i : ι) : U i ≤ O := hU ▸ le_iSup U i
  have hVi (i : κ) : V i ≤ O := hV ▸ le_iSup V i
  have haU' (i : ι) : IsAffineOpen (U' i) :=
    (haU i).preimage_of_isOpenImmersion O.ι (by simpa using hUi i)
  have haV' (i : κ) : IsAffineOpen (V' i) :=
    (haV i).preimage_of_isOpenImmersion O.ι (by simpa using hVi i)
  let := image_quasiIso O.ι U' V' r' M hU' hV' haU' haV'
  have heU : O.ι.opensFunctor.obj ∘ U' = U := by
    funext i
    change O.ι ''ᵁ (O.ι ⁻¹ᵁ U i) = U i
    rw [O.ι.image_preimage_eq_opensRange_inf, O.opensRange_ι, inf_eq_right.mpr (hUi i)]
  have heV : O.ι.opensFunctor.obj ∘ V' = V := by
    funext i
    change O.ι ''ᵁ (O.ι ⁻¹ᵁ V i) = V i
    rw [O.ι.image_preimage_eq_opensRange_inf, O.opensRange_ι, inf_eq_right.mpr (hVi i)]
  exact Cech.RefinementFamilyEquality.Family.quasiIso
    (Cech.RefinementProductCoordinates.mappedCover O.ι.opensFunctor U' V' r')
    r M.presheaf heU heV rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.CoverRefinementQuasiIso.Cech
