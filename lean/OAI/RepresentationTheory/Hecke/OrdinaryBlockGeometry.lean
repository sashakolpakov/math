import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels

/-! # Ordinary Block Geometry -/

namespace OAI.RepresentationTheory.Hecke.OrdinaryBlockGeometry.OrdinaryCharacterIntrinsic

noncomputable section

/-! Pure etale ordinary splittings give finite etale structural maps
on the original block, by transport through the actual group isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels.Construction

variable (R : Type) [CommRing R] (q n r : ℕ) [NeZero q]
  {B : Grp (Over (Spec (.of R)))} (e : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting R B q n 0 r)

include e in
theorem pureEtaleBlock_geometry : IsFinite B.X.hom ∧ Etale B.X.hom := by
  let M := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock R q n 0
  let E := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock R q n r
  have : IsIso M.X.hom := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CompactKernels.Construction.multiplicativeZero_structural_isIso R q n
  have : IsFinite E.X.hom := (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock_finiteLocallyFree R q n r).1
  have : Etale E.X.hom := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme_etale _ _
  have : IsFinite (M ⊗ E).X.hom := by
    change IsFinite (pullback.fst M.X.hom E.X.hom ≫ M.X.hom)
    infer_instance
  have : Etale (M ⊗ E).X.hom := by
    change Etale (pullback.fst M.X.hom E.X.hom ≫ M.X.hom)
    infer_instance
  let f : B.X.left ⟶ (M ⊗ E).X.left := e.hom.hom.hom.left
  have : IsIso f := inferInstanceAs
    (IsIso (((Grp.forget (Over (Spec (.of R)))) ⋙ Over.forget _).map e.hom))
  have hw : f ≫ (M ⊗ E).X.hom = B.X.hom := e.hom.hom.hom.w
  exact ⟨(congrArg IsFinite hw).mp inferInstance, (congrArg Etale hw).mp inferInstance⟩

end

end OAI.RepresentationTheory.Hecke.OrdinaryBlockGeometry.OrdinaryCharacterIntrinsic
