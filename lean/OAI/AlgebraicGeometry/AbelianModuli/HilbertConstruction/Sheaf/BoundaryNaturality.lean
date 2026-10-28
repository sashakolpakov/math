import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryCokernel

/-! # Boundary Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryNaturality.IntrinsicCech

noncomputable section

/-! Naturality of the section boundary and its cokernel comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{u}}
    {S T : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}

private def sectionCohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0 :
      _ ⥤ AddCommGrpCat.{u}).obj F) ≃+ F.obj.obj (op ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop

/-- The section boundary respects every map of short exact sequences. -/
theorem sheafSectionBoundary_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (x : S.X₃.obj.obj (op ⊤)) :
    BoundaryCokernel.IntrinsicCech.sheafSectionBoundary hT (φ.τ₃.hom.app (op ⊤) x) =
      CategoryTheory.Sheaf.H.map φ.τ₁ 1 (BoundaryCokernel.IntrinsicCech.sheafSectionBoundary hS x) := by
  change CohomologyExact.SheafCohomologyExact.Cohomology.δ.{u} hT 0 1 rfl ((sectionCohomologyEquiv T.X₃).symm
    (φ.τ₃.hom.app (op ⊤) x)) = _
  dsimp only [sectionCohomologyEquiv]
  erw [← CategoryTheory.Sheaf.H.equiv₀_symm_naturality]
  exact CohomologyExact.SheafCohomologyExact.Cohomology.δ_naturality.{u} 0 1 rfl hS hT φ _

/-- The cokernel comparison is induced by the actual section boundary. -/
theorem sheafSectionBoundaryCokernelIso_π (hS : S.ShortExact)
    (hS₁ : Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₂))) :
    cokernel.π (S.g.hom.app (op ⊤)) ≫ (BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso.{u} hS hS₁).hom =
      AddCommGrpCat.ofHom (BoundaryCokernel.IntrinsicCech.sheafSectionBoundary hS) := by
  let : Epi (BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryShortComplex hS).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (BoundaryCokernel.IntrinsicCech.sheafSectionBoundary_surjective hS hS₁)
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (S.g.hom.app (op ⊤)))
    (BoundaryCokernel.IntrinsicCech.sheafSectionBoundary_exact hS).gIsCokernel WalkingParallelPair.one

def sheafSectionCokernelMap (φ : S ⟶ T) :
    cokernel (S.g.hom.app (op ⊤)) ⟶ cokernel (T.g.hom.app (op ⊤)) :=
  cokernel.map (S.g.hom.app (op ⊤)) (T.g.hom.app (op ⊤))
    (φ.τ₂.hom.app (op ⊤)) (φ.τ₃.hom.app (op ⊤))
    (congrArg (fun k : S.X₂ ⟶ T.X₃ => k.hom.app (op ⊤)) φ.comm₂₃.symm)

private def rebundleGroupHom {A B : AddCommGrpCat.{u}} (f : A ⟶ B) :
    AddCommGrpCat.of A ⟶ AddCommGrpCat.of B := f

private def firstCohomologyMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj F)) ⟶
    AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj G)) :=
  rebundleGroupHom ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
    _ ⥤ AddCommGrpCat.{u}).map f)

theorem sheafSectionBoundaryCokernelIso_naturality
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (hS₁ : Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₂)))
    (hT₁ : Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj T.X₂))) :
    sheafSectionCokernelMap.{u} φ ≫ (BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso.{u} hT hT₁).hom =
      (BoundaryCokernel.IntrinsicCech.sheafSectionBoundaryCokernelIso.{u} hS hS₁).hom ≫
        firstCohomologyMap φ.τ₁ := by
  apply (cancel_epi (cokernel.π (S.g.hom.app (op ⊤)))).mp
  rw [← Category.assoc, sheafSectionCokernelMap, cokernel.π_desc, Category.assoc,
    sheafSectionBoundaryCokernelIso_π, ← Category.assoc, sheafSectionBoundaryCokernelIso_π]
  ext x
  exact sheafSectionBoundary_naturality hS hT φ x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryNaturality.IntrinsicCech
