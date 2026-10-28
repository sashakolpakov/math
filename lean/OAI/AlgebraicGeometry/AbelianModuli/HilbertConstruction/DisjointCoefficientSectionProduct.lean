import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyModuleSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Disjoint Coefficient Section Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointCoefficientSectionProduct

noncomputable section

/-! Sections on a disjoint open cover form the product of the actual
section modules, with the original coefficient-ring action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
universe u

def disjointCoefficientSectionProductEquiv
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : R →+* Γ(X, ⊤)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hdis : Pairwise (fun i j => Disjoint (U i) (U j))) :
    (Coefficient.SectionEvaluation.coefficientSectionFunctor c ⊤).obj M ≃ₗ[R]
      ∀ i, (Coefficient.SectionEvaluation.coefficientSectionFunctor c (U i)).obj M := by
  classical
  let P := Coefficient.ModulePresheaf.coefficientModulePresheaf c M
  let f := LinearMap.pi (fun i => (P.map (U i).leTop.op).hom)
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr (hU x)
  have hglue (s : ∀ i, (Coefficient.SectionEvaluation.coefficientSectionFunctor c (U i)).obj M) :
      ∃! m : (Coefficient.SectionEvaluation.coefficientSectionFunctor c ⊤).obj M, f m = s := by
    have hs : ∀ i j,
        M.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i) =
        M.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j) := by
      intro i j
      by_cases hij : i = j
      · subst j
        rfl
      · exact (EmptyModuleSections.moduleSections_subsingleton_of_empty M (disjoint_iff.mp (hdis hij))).elim _ _
    have hs' : TopCat.Presheaf.IsCompatible F.obj U (fun i => s i) := by
      intro i j
      exact hs i j
    obtain ⟨m, hm, huniq⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop) hcover (fun i => s i) hs'
    refine ⟨m, funext hm, ?_⟩
    intro m' hm'
    exact huniq m' (fun i => congrFun hm' i)
  apply LinearEquiv.ofBijective f
  constructor
  · intro m n h
    obtain ⟨z, _, hz⟩ := hglue (f m)
    exact (hz m rfl).trans (hz n h.symm).symm
  · intro s
    obtain ⟨m, hm, _⟩ := hglue s
    exact ⟨m, hm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DisjointCoefficientSectionProduct
