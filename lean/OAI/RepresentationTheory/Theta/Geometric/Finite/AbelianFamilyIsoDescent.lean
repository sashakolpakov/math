import OAI.RepresentationTheory.Theta.Geometric.Complex.AlgebraParameterMap
import OAI.RepresentationTheory.Theta.Geometric.Finite.ParameterLineIsoDescent
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Abelian Family Iso Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.AbelianFamilyIsoDescent

noncomputable section

section

/-! Two actual line bundles on an abelian family which become
isomorphic after an arbitrary parameter extension are already
isomorphic over a finitely generated parameter subalgebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem exists_fg_abelian_family_lineIso
    {B R : Type} [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R]
    {n : ℕ} (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (L N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⊗ A.scheme).left)
    (a : (L.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A.scheme).left).sheaf ≅
      (N.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A.scheme).left).sheaf) :
    ∃ S : Subalgebra B R, S.FG ∧
      Nonempty ((L.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A.scheme).left).sheaf ≅
        (N.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A.scheme).left).sheaf) := by
  let T := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B
  let h := (fst T A.scheme).left
  have : CompactSpace T.left := inferInstanceAs (CompactSpace (Spec (.of B)))
  have : CompactSpace (T ⊗ A.scheme).left := by
    change CompactSpace (pullback T.hom A.scheme.hom : Scheme)
    infer_instance
  have : Flat h := by
    change Flat (pullback.fst T.hom A.scheme.hom)
    infer_instance
  let HR := Complex.AlgebraParameterMap.complexAlgebraParameterMap_product_isPullback B R A.scheme
  let ar := AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HR.isoPullback.inv
    (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A.scheme).left (ParameterOpenCharts.parameterProjection h R) HR.isoPullback_inv_fst a
  obtain ⟨S, hS, ⟨b⟩⟩ := ParameterLineIsoDescent.exists_fg_parameter_lineIso h L N ar
  let HS := Complex.AlgebraParameterMap.complexAlgebraParameterMap_product_isPullback B S A.scheme
  exact ⟨S, hS, ⟨AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HS.isoPullback.hom (ParameterOpenCharts.parameterProjection h S)
    (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A.scheme).left HS.isoPullback_hom_fst b⟩⟩

end

/-! Isomorphisms of actual line bundles on constant quasi-compact flat
families descend to finitely generated parameter algebras. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem exists_fg_constant_family_lineIso
    {B R : Type} [CommRing B] [CommRing R] [Algebra ℂ B] [Algebra ℂ R]
    [Algebra B R] [IsScalarTower ℂ B R]
    (A : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Flat A.hom] [QuasiCompact A.hom]
    (L N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⊗ A).left)
    (a : (L.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A).left).sheaf ≅
      (N.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A).left).sheaf) :
    ∃ S : Subalgebra B R, S.FG ∧
      Nonempty ((L.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A).left).sheaf ≅
        (N.pullback (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A).left).sheaf) := by
  let T := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B
  let h := (fst T A).left
  have : CompactSpace T.left := inferInstanceAs (CompactSpace (Spec (.of B)))
  have : CompactSpace (T ⊗ A).left := by
    change CompactSpace (pullback T.hom A.hom : Scheme)
    infer_instance
  have : Flat h := by
    change Flat (pullback.fst T.hom A.hom)
    infer_instance
  let HR := Complex.AlgebraParameterMap.complexAlgebraParameterMap_product_isPullback B R A
  let ar := AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HR.isoPullback.inv
    (Complex.AlgebraParameterMap.complexAlgebraParameterMap B R ▷ A).left (ParameterOpenCharts.parameterProjection h R) HR.isoPullback_inv_fst a
  obtain ⟨S, hS, ⟨b⟩⟩ := ParameterLineIsoDescent.exists_fg_parameter_lineIso h L N ar
  let HS := Complex.AlgebraParameterMap.complexAlgebraParameterMap_product_isPullback B S A
  exact ⟨S, hS, ⟨AlgebraicGeometry.Isogenies.NeighborCounting.FramedPullback.pullbackIsoTo HS.isoPullback.hom (ParameterOpenCharts.parameterProjection h S)
    (Complex.AlgebraParameterMap.complexAlgebraParameterMap B S ▷ A).left HS.isoPullback_hom_fst b⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.AbelianFamilyIsoDescent
