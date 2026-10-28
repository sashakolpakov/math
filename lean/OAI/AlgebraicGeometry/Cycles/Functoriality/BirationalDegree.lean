import OAI.AlgebraicGeometry.Cycles.Functoriality.UnitCap
import OAI.AlgebraicGeometry.Cycles.Functoriality.ResidueDegree

/-! # Birational Degree -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.BirationalDegree.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- A morphism agreeing with a dense-open isomorphism sends generic
point to generic point. -/
theorem genericPoint_of_partialIso
    {S T : Scheme} [IsIntegral S] [IsIntegral T]
    (π : S ⟶ T) (e : S.PartialIso T)
    (he : e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) :
    π (genericPoint S) = genericPoint T := by
  let : Nonempty e.source := e.dense_source.nonempty.to_subtype
  let : Nonempty e.target := e.dense_target.nonempty.to_subtype
  have hs := genericPoint_eq_of_isOpenImmersion e.source.ι
  have ht := genericPoint_eq_of_isOpenImmersion e.target.ι
  have hi := genericPoint_eq_of_isOpenImmersion e.iso.hom
  exact (congrArg π hs.symm).trans
    ((congrArg (fun k : e.source.toScheme ⟶ T => k (genericPoint e.source.toScheme)) he).trans
      ((congrArg e.target.ι hi).trans ht))

/-- An immersion identifies residue fields, so its residue degree is one. -/
theorem residueDegree_eq_one_of_immersion {S T : Scheme}
    (i : S ⟶ T) [SurjectiveOnStalks i] (x : S) : i.residueDegree x = 1 := by
  have h := ResidueDegree.Construction.residueDegree_pre_immersion i (𝟙 T) x
  simpa only [Category.comp_id, Scheme.Hom.residueDegree_id] using h

/-- The generic degree of a morphism agreeing with a dense-open
isomorphism is one, calculated with the actual residue field maps. -/
theorem residueDegree_of_partialIso
    {S T : Scheme} [IsIntegral S] [IsIntegral T]
    (π : S ⟶ T) (e : S.PartialIso T)
    (he : e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) :
    π.residueDegree (genericPoint S) = 1 := by
  let : Nonempty e.source := e.dense_source.nonempty.to_subtype
  have h := congrArg
    (fun k : e.source.toScheme ⟶ T => k.residueDegree (genericPoint e.source.toScheme)) he
  rw [ResidueDegree.Construction.residueDegree_pre_immersion, ResidueDegree.Construction.residueDegree_post_immersion,
    genericPoint_eq_of_isOpenImmersion] at h
  exact h.trans (residueDegree_eq_one_of_immersion e.iso.hom _)

/-- A genuine resolution morphism maps its source generic point to
the generic point of the prescribed support. -/
theorem resolves_genericPoint
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (g : R.toOver ⟶ X.toOver) (hres : UnitCap.Resolves g Z) :
    g.left (genericPoint R.carrier) = Z.genericPoint := by
  obtain ⟨π, hπ, _, _, e, he⟩ := hres
  have hη := genericPoint_of_partialIso π e he
  exact (congrArg (fun k : R.carrier ⟶ X.carrier => k (genericPoint R.carrier)) hπ).symm.trans
    ((congrArg Z.inclusion hη).trans Z.inclusion_genericPoint)

/-- A genuine resolution has generic residue degree one in the ambient target. -/
theorem resolves_residueDegree
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (g : R.toOver ⟶ X.toOver) (hres : UnitCap.Resolves g Z) :
    g.left.residueDegree (genericPoint R.carrier) = 1 := by
  obtain ⟨π, hπ, _, _, e, he⟩ := hres
  have h := residueDegree_of_partialIso π e he
  have hc := ResidueDegree.Construction.residueDegree_post_immersion π Z.inclusion (genericPoint R.carrier)
  exact (congrArg (fun k : R.carrier ⟶ X.carrier => k.residueDegree (genericPoint R.carrier)) hπ).symm.trans
    (hc.trans h)

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.BirationalDegree.Construction
