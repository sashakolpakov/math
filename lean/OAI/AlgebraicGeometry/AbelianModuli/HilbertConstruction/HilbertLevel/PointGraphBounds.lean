import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.GroupBoundsCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DataEmbeddingRecovery

/-! # Point Graph Bounds -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointGraphBounds

noncomputable section

/-! The original universal full-level Hilbert family has the prescribed
multiplication and inversion graph polynomials at every test point. The
proof reads the actual bounded operation datum and uses its native
embedding-preserving group recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

local instance pointBoundsPullbackFlat {S T : Scheme.{u}}
    (f : T ⟶ S) (X : Over S) [Flat X.hom] : Flat ((Over.pullback f).obj X).hom :=
  inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd X.hom f))
local instance pointBoundsPullbackFinitePresentation {S T : Scheme.{u}}
    (f : T ⟶ S) (X : Over S) [LocallyOfFinitePresentation X.hom] :
    LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd X.hom f))
local instance pointBoundsPullbackSeparated {S T : Scheme.{u}}
    (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] : IsSeparated ((Over.pullback f).obj X).hom :=
  inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd X.hom f))

section GroupTransport
variable {S : Scheme.{u}} {X Y : Over S} [GrpObj X] [GrpObj Y]
    (e : X ≅ Y) [IsMonHom e.hom]

theorem FamilyGroupOperations.ofGrpObj_ofIso :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X).ofIso e = FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj Y := by
  apply FamilyGroup.Operations.FamilyGroupOperations.ext
  · exact IsMonHom.one_hom e.hom
  · change (e.inv ⊗ₘ e.inv) ≫ μ[X] ≫ e.hom = μ[Y]
    rw [IsMonHom.mul_hom e.hom, ← Category.assoc, tensorHom_comp_tensorHom,
      e.inv_hom_id, id_tensorHom_id, Category.id_comp]
  · change e.inv ≫ ι[X] ≫ e.hom = ι[Y]
    rw [GrpObj.inv_hom, e.inv_hom_id_assoc]
end GroupTransport

private theorem inverse_embedding {C : Type*} [Category* C]
    {X Y Z : C} (e : X ≅ Y) (i : Y ⟶ Z) (j : X ⟶ Z)
    (h : e.hom ≫ i = j) : e.inv ≫ j = i :=
  (congrArg (fun a => e.inv ≫ a) h.symm).trans (e.inv_hom_id_assoc i)

private theorem groupBounds_transport
    {S : Scheme.{u}} {X Y : Over S} [GrpObj X] [GrpObj Y]
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
    [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]
    {n : ℕ} (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (e : X ≅ Y) [IsMonHom e.hom] (h : e.hom ≫ j = i) (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X).ProjectiveGraphBounds
      ⟨n, i, inferInstance⟩ Hm Hi) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj Y).ProjectiveGraphBounds ⟨n, j, inferInstance⟩ Hm Hi := by
  have hb' := FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofIso i j e h
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X) Hm Hi hb
  exact (congrArg (fun D : FamilyGroup.Operations.FamilyGroupOperations Y =>
    D.ProjectiveGraphBounds ⟨n, j, inferInstance⟩ Hm Hi)
      (FamilyGroupOperations.ofGrpObj_ofIso e)).mp hb'

private theorem groupBounds_recovery
    {S : Scheme.{u}} {X Y : Over S} [GrpObj X] [GrpObj Y]
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
    [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y)
    (e : Y ≅ X) [IsMonHom e.hom] (hn : P.dimension = Q.dimension)
    (h : HEq (e.hom.left ≫ P.embedding.left) Q.embedding.left) (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj X).ProjectiveGraphBounds P Hm Hi) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj Y).ProjectiveGraphBounds Q Hm Hi := by
  rcases P with ⟨n, i, hi⟩
  rcases Q with ⟨m, j, hj⟩
  cases hn
  have he : e.hom ≫ i = j := by
    apply Over.OverMorphism.ext
    exact eq_of_heq h
  let : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  exact @groupBounds_transport S X Y inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance n
    i j hi hj e.symm inferInstance (inverse_embedding e i j he) Hm Hi hb

private theorem abelianBounds_recovery
    {S : Scheme.{u}} {g h : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (Q : Projective.ProjectivePresentations.ProjectivePresentation B.scheme)
    (e : B.scheme ≅ A.scheme) [IsMonHom e.hom] (hn : P.dimension = Q.dimension)
    (he : HEq (e.hom.left ≫ P.embedding.left) Q.embedding.left) (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj B.scheme).ProjectiveGraphBounds Q Hm Hi :=
  groupBounds_recovery P Q e hn he Hm Hi hb

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ)
    (g : ℕ) (Hm Hi : Polynomial ℚ)

omit [AlgebraicGeometry.IsNoetherian S] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData.FixedDimensionHilbertAbelianData.graphBounds {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj (D.abelianScheme S n H g Hm Hi).scheme).ProjectiveGraphBounds
      (D.val.projective S n H g Hm Hi) Hm Hi := by
  change D.val.2.val.val.ProjectiveGraphBounds
    ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange D.val.1.left) Hm Hi
  exact (Intrinsic.GroupBoundsCriterion.boundedNativeGroupOperations_property_iff
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g) Hm Hi
    (Over.mk D.val.1.left) D.val.2.val.val).mp D.val.2.val.property

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem abelianDataBounds_recovery {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n H g Hm Hi T)
    (B₀ : Abelian.Schemes.AbelianScheme g T.left) (Q : Projective.ProjectivePresentations.ProjectivePresentation B₀.scheme)
    (e : B₀.scheme ≅ (D.abelianScheme S n H g Hm Hi).scheme) [IsMonHom e.hom]
    (hn : (D.val.projective S n H g Hm Hi).dimension = Q.dimension)
    (he : HEq (e.hom.left ≫ (D.val.projective S n H g Hm Hi).embedding.left) Q.embedding.left) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj B₀.scheme).ProjectiveGraphBounds Q Hm Hi :=
  abelianBounds_recovery (D.abelianScheme S n H g Hm Hi) B₀
    (D.val.projective S n H g Hm Hi) Q e hn he Hm Hi (D.graphBounds S n H g Hm Hi)

theorem fixedDimensionHilbertAbelianPoint_graphBounds {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n H g Hm Hi) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback y.left).scheme).ProjectiveGraphBounds
        ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange y.left)
        Hm Hi := by
  let D := FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n H g Hm Hi T y
  let B₀ : Abelian.Schemes.AbelianScheme g T.left := (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback y.left
  let e : B₀.scheme ≅ (D.abelianScheme S n H g Hm Hi).scheme :=
    Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n H g Hm Hi y
  let Q : Projective.ProjectivePresentations.ProjectivePresentation B₀.scheme :=
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange y.left
  let : IsMonHom e.hom := Fixed.UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso_isMonHom S n H g Hm Hi y
  exact abelianDataBounds_recovery S n H g Hm Hi D B₀ Q e rfl
    (heq_of_eq (Fixed.DataEmbeddingRecovery.abelianPointFamilyIso_embedding_left S n H g Hm Hi y))

private theorem abelianPointBounds_recovery {T : Over S}
    (a : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n H g Hm Hi)
    (B₀ : Abelian.Schemes.AbelianScheme g T.left) (Q : Projective.ProjectivePresentations.ProjectivePresentation B₀.scheme)
    (e : B₀.scheme ≅ ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback a.left).scheme)
    [IsMonHom e.hom]
    (hn : ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange a.left).dimension = Q.dimension)
    (he : HEq (e.hom.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange a.left).embedding.left) Q.embedding.left) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj B₀.scheme).ProjectiveGraphBounds Q Hm Hi :=
  abelianBounds_recovery ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback a.left) B₀
    ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n H g Hm Hi).baseChange a.left)
    Q e hn he Hm Hi (fixedDimensionHilbertAbelianPoint_graphBounds S n H g Hm Hi a)

variable (N : ℕ) [NeZero N]

theorem fixedDimensionHilbertFullLevelPoint_graphBounds {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n H g Hm Hi N) :
    (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback y.left).scheme).ProjectiveGraphBounds
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange y.left)
        Hm Hi := by
  let a := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n H g Hm Hi N T y).1
  let B₀ : Abelian.Schemes.AbelianScheme g T.left := (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback y.left
  let e : B₀.scheme ≅ ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n H g Hm Hi).pullback a.left).scheme :=
    Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n H g Hm Hi N y
  let Q : Projective.ProjectivePresentations.ProjectivePresentation B₀.scheme :=
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange y.left
  let : IsMonHom e.hom := Fixed.LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso_isMonHom S n H g Hm Hi N y
  exact abelianPointBounds_recovery S n H g Hm Hi a B₀ Q e rfl
    (heq_of_eq (Fixed.DataEmbeddingRecovery.fullLevelPointFamilyIso_embedding_left S n H g Hm Hi N y))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PointGraphBounds
