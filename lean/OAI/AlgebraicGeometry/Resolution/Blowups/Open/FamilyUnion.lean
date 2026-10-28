import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.ModeledNormalChart

/-! # Family Union -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Open.FamilyUnion.Construction

noncomputable section

/-! An actual family of open maps covers its open union, with the original maps retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {ι : Type} (U : ι → Scheme) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]

def openFamilyUnion : X.Opens := ⨆ i, (j i).opensRange

def openFamilyUnionMap (i : ι) : U i ⟶ (openFamilyUnion U j).toScheme :=
  IsOpenImmersion.lift (openFamilyUnion U j).ι (j i) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, x, rfl⟩)

theorem openFamilyUnionMap_over (i : ι) :
    openFamilyUnionMap U j i ≫ (openFamilyUnion U j).ι = j i :=
  IsOpenImmersion.lift_fac _ _ _

instance openFamilyUnionMap_isOpenImmersion (i : ι) : IsOpenImmersion (openFamilyUnionMap U j i) := by
  let : IsOpenImmersion (openFamilyUnionMap U j i ≫ (openFamilyUnion U j).ι) := by
    rw [openFamilyUnionMap_over]
    infer_instance
  exact IsOpenImmersion.of_comp _ (openFamilyUnion U j).ι

theorem openFamilyUnionMap_covers (x : (openFamilyUnion U j).toScheme) :
    ∃ i y, openFamilyUnionMap U j i y = x := by
  obtain ⟨i, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
  refine ⟨i, y, ?_⟩
  apply (openFamilyUnion U j).ι.isOpenEmbedding.injective
  have he := congrArg (fun f => f y) (openFamilyUnionMap_over U j i)
  exact he.trans hy

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Open.FamilyUnion.Construction
