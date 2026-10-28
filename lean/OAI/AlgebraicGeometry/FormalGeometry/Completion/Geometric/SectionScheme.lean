import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.SectionAlgebra
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.BaseAlgebraPoints
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Section Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric

noncomputable section

/-! The derived section algebra gives an actual affine scheme of finite
type, with classification of global sections natural for geometric pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} {M : X.Modules}
  (D : SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π M)

def SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.scheme : Over S := Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraScheme S D.algebra

instance SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.scheme_isAffine : IsAffine D.scheme.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of D.algebra)))

instance SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.scheme_affineHom : IsAffineHom D.scheme.hom := inferInstance

instance SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.scheme_locallyOfFiniteType : LocallyOfFiniteType D.scheme.hom := by
  have hr : (Completion.Affine.BaseAlgebraPoints.Construction.affineBaseAlgebraMap S D.algebra).hom.FiniteType :=
    RingHom.finiteType_algebraMap.mpr D.finiteType
  have : LocallyOfFiniteType (Spec.map (Completion.Affine.BaseAlgebraPoints.Construction.affineBaseAlgebraMap S D.algebra)) :=
    HasRingHomProperty.Spec_iff.mpr hr
  change LocallyOfFiniteType (Spec.map (Completion.Affine.BaseAlgebraPoints.Construction.affineBaseAlgebraMap S D.algebra) ≫ S.isoSpec.inv)
  infer_instance

def SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.sectionPointEquiv {Y T : Scheme.{u}} [IsAffine T]
    (f : Y ⟶ X) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ π g) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤) ≃
      (Over.mk g ⟶ D.scheme) := by
  letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  exact (D.equivalence Y T f ρ g hp).trans (Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S D.algebra (Over.mk g)).symm

theorem SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.sectionPointEquiv_natural {Y Z T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (f : Y ⟶ X) (j : Z ⟶ Y) (ρ : Y ⟶ T) (τ : Z ⟶ T') (g : T ⟶ S) (t : T' ⟶ T)
    (hp : IsPullback f ρ π g) (hj : j ≫ ρ = τ ≫ t) (ho : IsPullback (j ≫ f) τ π (t ≫ g))
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op ⊤)) :
    D.sectionPointEquiv (j ≫ f) τ (t ≫ g) ho (GlobalSectionComposition.Construction.globalSectionCompositePullback f j M s) =
      (Over.homMk t rfl : Over.mk (t ≫ g) ⟶ Over.mk g) ≫ D.sectionPointEquiv f ρ g hp s := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) Γ(T', ⊤) := (t ≫ g).appTop.hom.toAlgebra
  apply (Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S D.algebra (Over.mk (t ≫ g))).injective
  change Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S D.algebra (Over.mk (t ≫ g))
    ((Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S D.algebra (Over.mk (t ≫ g))).symm
      (D.equivalence Z T' (j ≫ f) τ (t ≫ g) ho (GlobalSectionComposition.Construction.globalSectionCompositePullback f j M s))) = _
  rw [Equiv.apply_symm_apply, Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv_composite]
  change D.equivalence Z T' (j ≫ f) τ (t ≫ g) ho (GlobalSectionComposition.Construction.globalSectionCompositePullback f j M s) =
    (ScalarKernelAlgebraNaturality.Construction.scalarTransitionAlgHomOfEq g.appTop.hom t.appTop.hom (t ≫ g).appTop.hom rfl).comp
      (Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S D.algebra (Over.mk g)
        ((Completion.Affine.BaseAlgebraPoints.Construction.affineAlgebraPointEquiv S D.algebra (Over.mk g)).symm (D.equivalence Y T f ρ g hp s)))
  rw [Equiv.apply_symm_apply]
  exact D.natural Y Z T T' f j ρ τ g t hp hj ho s

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric
