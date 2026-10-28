import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.RetractCopies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SectionValueAdditive

/-! # Retract Section Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite

noncomputable section

/-! A finite matrix identity decomposes every section into sections of
the source object. Surjectivity on global values is surjectivity on actual section maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.AlgebraicGeometry
open scoped BigOperators
universe u
variable {X : Scheme.{u}}

theorem RetractSectionFactorization.section_postcomp_surjective_of_global_surjective {M N : X.Modules}
    (f : M ⟶ N) (hf : Function.Surjective (f.app (⊤ : X.Opens))) :
    Function.Surjective (fun s : Line.Bundles.structureModule X ⟶ M => s ≫ f) := by
  intro t
  obtain ⟨v, hv⟩ := hf (Global.Sections.moduleSectionHomEquiv N t)
  refine ⟨(Global.Sections.moduleSectionHomEquiv M).symm v, (Global.Sections.moduleSectionHomEquiv N).injective ?_⟩
  change f.app ⊤ (Global.Sections.moduleSectionHomEquiv M ((Global.Sections.moduleSectionHomEquiv M).symm v)) = _
  rw [Equiv.apply_symm_apply]
  exact hv

theorem RetractCopies.FiniteRetractCopies.sections_factor {L M : X.Modules} (h : RetractCopies.FiniteRetractCopies L M)
    {N : X.Modules} (f : M ⟶ N)
    (hf : Function.Surjective (fun s : Line.Bundles.structureModule X ⟶ M => s ≫ f))
    (t : Line.Bundles.structureModule X ⟶ N) :
    ∃ (n : ℕ) (s : Fin n → (Line.Bundles.structureModule X ⟶ L)) (a : Fin n → (L ⟶ N)),
      t = ∑ i, s i ≫ a i := by
  obtain ⟨n, ι, π, he⟩ := h
  obtain ⟨v, rfl⟩ := hf t
  refine ⟨n, fun i => v ≫ π i, fun i => ι i ≫ f, ?_⟩
  calc
    v ≫ f = v ≫ (∑ i, π i ≫ ι i) ≫ f := by rw [he]; simp
    _ = ∑ i, (v ≫ π i) ≫ (ι i ≫ f) := by simp only [comp_sum, sum_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite
