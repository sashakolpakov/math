import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionEtaleAt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms

/-! # Complex Level -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

noncomputable section

/-! Construct full levels for the original projective complex abelian
scheme, by combining native torsion with the proved finite-etale group
splitting. Neither a marking nor a comparison is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

def constantValuesEquiv (G : Type) [Group G] : G ≃* LocallyConstant Foundations.Scheme.ProjectiveSpace.complexBase G where
  toFun := LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase
  invFun f := f default
  left_inv _ := rfl
  right_inv f := by
    apply LocallyConstant.ext
    intro x
    exact congrArg f (Subsingleton.elim default x)
  map_mul' _ _ := rfl

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)

/-- An actual projective embedding, TorsionQuotient, and the native exponential
construct a full ordered N-level on the original complex abelian scheme. -/
theorem exists_fullLevel (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (N : ℕ) [NeZero N] : Nonempty (A.FullLevel N) := by
  obtain ⟨hf, he⟩ := TorsionEtaleAt.TorsionEtale.torsion_finite_etale A (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) N
  let : IsFinite (A.torsionScheme N).hom := hf
  let : Etale (A.torsionScheme N).hom := he
  obtain ⟨G, hG, hfin, ⟨e⟩⟩ := Geometric.Splitting.GeometricSplitting.exists_constant_groupIso (A.torsionScheme N)
  let : Group G := hG
  let : Finite G := hfin
  let e' : HilbertConstruction.Constant.GroupMaps.constantGroupFunctor Foundations.Scheme.ProjectiveSpace.complexBase G ≅ A.torsionFunctor N :=
    e ≪≫ A.torsionSchemeYonedaIso N
  let ep : G ≃* A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) :=
    (constantValuesEquiv G).trans ((e'.app (.op (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))).groupIsoToMulEquiv)
  let ec : Multiplicative (Fin (2 * g) → ZMod N) ≃* A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) :=
    AddEquiv.toMultiplicativeLeft (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.torsionPointEquiv A P N)
  exact ⟨HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels (LocallyConstant.const Foundations.Scheme.ProjectiveSpace.complexBase (ec.trans ep.symm)) ≪≫ e'⟩

def fullLevel (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (N : ℕ) [NeZero N] : A.FullLevel N :=
  Classical.choice (exists_fullLevel A P N)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel
