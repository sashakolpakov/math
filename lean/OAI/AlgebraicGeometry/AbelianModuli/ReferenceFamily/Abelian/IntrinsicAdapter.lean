import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionScheme
import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothDimension
import OAI.AlgebraicGeometry.Betti.SmoothDimension

/-! # Intrinsic Adapter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter

noncomputable section

/-! Relate HilbertConstruction's actual complex abelian schemes to the native abelian
variety model. Integrality is proved from smoothness and connectedness;
the projective input is an actual closed embedding of the same scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase)

theorem carrier_integral : IsIntegral A.scheme.left := by
  have hc : ConnectedSpace A.scheme.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom
  let : ConnectedSpace A.scheme.left := hc
  let : IsLocallyNoetherian A.scheme.left := LocallyOfFiniteType.isLocallyNoetherian A.scheme.hom
  let : CompactSpace A.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.scheme.hom
  let : IsNoetherian A.scheme.left := ⟨⟩
  let x : A.scheme.left := Classical.choice inferInstance
  have hi := irreducibleComponent_mem_irreducibleComponents x
  have ho := Foundations.Scheme.LocalDomainComponents.isOpen_irreducibleComponent_of_stalkDomains
    (Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_stalk_isDomain A.scheme.hom) finite_irreducibleComponents_of_isNoetherian hi
  have he : irreducibleComponent x = Set.univ :=
    (show IsClopen (irreducibleComponent x) from ⟨isClosed_irreducibleComponent, ho⟩).eq_univ
      ⟨x, mem_irreducibleComponent⟩
  have hir : IsIrreducible (Set.univ : Set A.scheme.left) := he ▸ hi.1
  let : PreirreducibleSpace A.scheme.left := ⟨hir.2⟩
  let : IrreducibleSpace A.scheme.left := ⟨inferInstance⟩
  let : IsReduced A.scheme.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced A.scheme.hom
  exact isIntegral_of_irreducibleSpace_of_isReduced _

local instance : IsIntegral A.scheme.left := carrier_integral A

def native (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety where
  variety := ⟨{
    carrier := A.scheme.left
    structureMap := A.scheme.hom
    projective := P
    smooth := inferInstance }, carrier_integral A⟩
  group := A.group
  commutative := A.commutative

/-- The native object has exactly the original underlying scheme. -/
theorem native_carrier (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) :
    (native A P).toOver.left = A.scheme.left := rfl

def nativeOverIso (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) :
    (native A P).toOver ≅ A.scheme :=
  Over.isoMk (Iso.refl _) (Category.id_comp _)

/-- The intrinsic native dimension equals HilbertConstruction's stated relative dimension. -/
theorem dimension_eq : Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom = g := by
  let x : A.scheme.left := Classical.choice inferInstance
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := g) (f := A.scheme.hom) x
  have htop : U = ⊤ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      exact (Subsingleton.elim (A.scheme.hom x) y) ▸ e hx
  subst U
  let : Nonempty V := ⟨⟨x, hx⟩⟩
  let := Betti.AffineDimension.Realization.sectionBaseAlgebra A.scheme.hom V
  let : Algebra.IsStandardSmoothOfRelativeDimension g Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(A.scheme.left, V) := hstd
  let : Algebra.IsStandardSmooth Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(A.scheme.left, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  let : Algebra.IsStandardSmoothOfRelativeDimension
      (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.scheme.hom)
      Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤) Γ(A.scheme.left, V) :=
    Betti.SmoothDimension.Realization.affineStandardSmooth_dimension A.scheme.hom V hV inferInstance
  exact Foundations.Scheme.StandardSmoothDimension.Algebraic.standardSmooth_dimension_unique
    (R := Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) (S := Γ(A.scheme.left, V)) _ _

instance nativeOverIso_isMonHom (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) :
    IsMonHom (nativeOverIso A P).hom where
  one_hom := by
    apply Over.OverMorphism.ext
    exact Category.comp_id _
  mul_hom := by
    apply Over.OverMorphism.ext
    change μ[A.scheme].left ≫ 𝟙 _ =
      (CategoryTheory.MonoidalCategory.tensorHom
        (𝟙 A.scheme) (𝟙 A.scheme)).left ≫ μ[A.scheme].left
    simp only [CategoryTheory.MonoidalCategory.tensorHom_id,
      CategoryTheory.MonoidalCategory.id_whiskerRight, Over.id_left,
      Category.comp_id, Category.id_comp]

def nativePointEquiv (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (native A P).toOver ≃*
      A.Points (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) :=
  CategoryTheory.Hom.mulEquivCongrRight (nativeOverIso A P) (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)

def torsionAddEquiv (N : ℕ) :
    Additive (A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) ≃+
      TorsionCongruence.TorusTorsion.killedBy (Additive (A.Points (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase))) N where
  toFun x := ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
  invFun x := Additive.ofMul ⟨x.val.toMul, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The native lattice calculation gives the standard torsion group of
the original HilbertConstruction abelian scheme, with its exact relative dimension. -/
def torsionPointEquiv (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation A.scheme.left A.scheme.hom)
    (N : ℕ) [NeZero N] :
    (Fin (2 * g) → ZMod N) ≃+
      Additive (A.torsionPoints N (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) := by
  let : IsIntegral (native A P).toOver.left := (native A P).variety.property
  have hd : Betti.AffineDimension.Realization.functionFieldDifferentialDimension (native A P).toOver.hom = g :=
    dimension_eq A
  let reindex {m n : ℕ} (h : m = n) : (Fin (2 * m) → ZMod N) ≃+ (Fin (2 * n) → ZMod N) :=
    h ▸ AddEquiv.refl _
  exact ((reindex hd.symm).trans (Intrinsic.Torsion.IntrinsicTorsion.nativeTorsionEquiv (native A P) N)).trans
    ((TorsionCongruence.TorusTorsion.killedByEquiv (nativePointEquiv A P).toAdditive N).trans
    (torsionAddEquiv A N).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter
