import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AcyclicResolutionDimensionShift

/-! # Boundary Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech

noncomputable section

/-! If the middle term of a short exact sheaf sequence has vanishing first cohomology, its section cokernel is the actual first cohomology of the left term. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CohomologyExact.SheafCohomologyExact.Cohomology
variable {X : TopCat.{u}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)

private def sheafSectionsEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0 :
      _ ⥤ AddCommGrpCat.{u}).obj F) ≃+ F.obj.obj (op ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop

include hS

def sheafSectionBoundary : S.X₃.obj.obj (op ⊤) →+ ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
    _ ⥤ AddCommGrpCat.{u}).obj S.X₁) :=
  (CohomologyExact.SheafCohomologyExact.Cohomology.δ.{u} hS 0 1 rfl).comp (sheafSectionsEquiv S.X₃).symm.toAddMonoidHom

theorem sheafSectionBoundary_comp (x : S.X₂.obj.obj (op ⊤)) :
    sheafSectionBoundary hS (S.g.hom.app (op ⊤) x) = 0 := by
  change CohomologyExact.SheafCohomologyExact.Cohomology.δ.{u} hS 0 1 rfl ((sheafSectionsEquiv S.X₃).symm
    (S.g.hom.app (op ⊤) x)) = 0
  dsimp only [sheafSectionsEquiv]
  erw [← CategoryTheory.Sheaf.H.equiv₀_symm_naturality]
  exact CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_comp_zero₃.{u} hS 0 1 rfl _

def sheafSectionBoundaryShortComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (S.g.hom.app (op ⊤)) (AddCommGrpCat.ofHom (sheafSectionBoundary hS)) (by
    ext x
    exact sheafSectionBoundary_comp hS x)

theorem sheafSectionBoundary_exact : (sheafSectionBoundaryShortComplex hS).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_equiv₀_exact₃.{u} hS isTerminalTop x hx

theorem sheafSectionBoundary_surjective
    (hH : Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₂))) :
    Function.Surjective (sheafSectionBoundary hS) := by
  let : Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₂)) := hH
  intro y
  have hz : ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).map S.f) y = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := CohomologyExact.SheafCohomologyExact.Cohomology.longSequence_exact₁_explicit.{u} hS 0 1 rfl y hz
  refine ⟨sheafSectionsEquiv S.X₃ x, ?_⟩
  change CohomologyExact.SheafCohomologyExact.Cohomology.δ.{u} hS 0 1 rfl ((sheafSectionsEquiv S.X₃).symm
    (sheafSectionsEquiv S.X₃ x)) = y
  exact (congrArg (CohomologyExact.SheafCohomologyExact.Cohomology.δ.{u} hS 0 1 rfl)
    ((sheafSectionsEquiv S.X₃).symm_apply_apply x)).trans hx

def sheafSectionBoundaryCokernelIso
    (hH : Subsingleton (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
      _ ⥤ AddCommGrpCat.{u}).obj S.X₂))) :
    cokernel (S.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1 :
    _ ⥤ AddCommGrpCat.{u}).obj S.X₁)) := by
  let T := sheafSectionBoundaryShortComplex hS
  have : Epi T.g := (AddCommGrpCat.epi_iff_surjective T.g).mpr (sheafSectionBoundary_surjective hS hH)
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel T.f)
    (sheafSectionBoundary_exact hS).gIsCokernel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.BoundaryCokernel.IntrinsicCech
