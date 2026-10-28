import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitGroup

/-! # Group Splitting At -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupSplittingAt.GroupSplitting

noncomputable section

/-! Construct group-compatible etale trivializations from finite etaleness
of the actual representing scheme. The finite group is recovered from
the actual fiber operations, not supplied as an input marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S S' : Scheme.{0}} (H : Over S) [GrpObj H]

/-- The actual scheme pullback represents restriction of the group-valued
functor to the new base. -/
def pullbackRepresentable (u : S' ⟶ S) :
    ((Over.map u).op ⋙ yonedaGrpObj H ⋙ forget GrpCat).RepresentableBy
      ((Over.pullback u).obj H) where
  homEquiv {T} := ((Over.mapPullbackAdj u).homEquiv T H).symm
  homEquiv_comp j f := by
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _

@[instance_reducible]
def pullbackGroup (u : S' ⟶ S) : GrpObj ((Over.pullback u).obj H) :=
  GrpObj.ofRepresentableBy _ ((Over.map u).op ⋙ yonedaGrpObj H)
    (pullbackRepresentable H u)

def pullbackYonedaIso (u : S' ⟶ S) :
    letI := pullbackGroup H u
    yonedaGrpObj ((Over.pullback u).obj H) ≅ (Over.map u).op ⋙ yonedaGrpObj H := by
  let := pullbackGroup H u
  exact yonedaGrpObjIsoOfRepresentableBy _ ((Over.map u).op ⋙ yonedaGrpObj H)
    (pullbackRepresentable H u)

/-- Every finite etale group scheme has group-compatible etale local
trivializations. The group law on the finite label set is constructed. -/
theorem exists_group_splitting_at [IsFinite H.hom] [Etale H.hom] (s : S) :
    ∃ (T : Scheme.{0}) (u : T ⟶ S), Etale u ∧ s ∈ Set.range u ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G), Nonempty
        (HilbertConstruction.Constant.GroupMaps.constantGroupFunctor T G ≅ (Over.map u).op ⋙ yonedaGrpObj H) := by
  obtain ⟨R, _, u, hu, ⟨t, ht⟩, r, ⟨e⟩⟩ :=
    SchemeSplitting.EtaleSplitting.exists_scheme_splitting_at H s
  let := pullbackGroup H u
  let U := SplitGroup.SplitGroupLabels.tableNeighborhood e t
  let v := U.ι
  let := SplitGroup.SplitGroupLabels.groupAt e t
  have hv : Etale v := inferInstance
  refine ⟨U.toScheme, v ≫ u, inferInstance, ⟨⟨t, rfl⟩, ht⟩,
    Fin r, inferInstance, inferInstance, ⟨?_⟩⟩
  let a := SplitGroup.SplitGroupLabels.localGroupIso e t
  let b := Functor.isoWhiskerLeft (Over.map v).op (pullbackYonedaIso H u)
  have hcomp : (Over.map v).op ⋙ ((Over.map u).op ⋙ yonedaGrpObj H) =
      (Over.map (v ≫ u)).op ⋙ yonedaGrpObj H := by
    rw [Over.mapComp_eq]
    rfl
  exact a ≪≫ b ≪≫ eqToIso hcomp

/-- Apply the construction to the actual abelian-scheme torsion kernel.
Only its finite etaleness is needed for the local finite-group splitting. -/
theorem exists_torsion_group_splitting_at {g N : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    [IsFinite (A.torsionScheme N).hom] [Etale (A.torsionScheme N).hom] (s : S) :
    ∃ (T : Scheme.{0}) (u : T ⟶ S), Etale u ∧ s ∈ Set.range u ∧
      ∃ (G : Type) (_ : Group G) (_ : Finite G), Nonempty
        (HilbertConstruction.Constant.GroupMaps.constantGroupFunctor T G ≅ (Over.map u).op ⋙ A.torsionFunctor N) := by
  obtain ⟨T, u, hu, hs, G, hG, hf, ⟨e⟩⟩ := exists_group_splitting_at (A.torsionScheme N) s
  exact ⟨T, u, hu, hs, G, hG, hf,
    ⟨e ≪≫ Functor.isoWhiskerLeft (Over.map u).op (A.torsionSchemeYonedaIso N)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupSplittingAt.GroupSplitting
