import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models

noncomputable section

/-! Concrete moduli-model and classifying properties. A model consists of
an actual scheme and a universal candidate family; representability is an
explicit predicate, never an unexplained constructor field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
  {X T : Over (Spec (.of K))}

/-- Isomorphism of a PEL family with the actual base change of another.
The equations refer to the scheme pullbacks, polarization map, Poincare
bundle, integral action, and ordered level of HilbertConstruction. -/
structure PELPullbackIso (U : PEL.Objects.PELObject P iota N X) (A : PEL.Objects.PELObject P iota N T)
    (f : T ⟶ X) where
  abelian : A.polarized.abelian.scheme ≅ (U.polarized.abelian.pullback f.left).scheme
  dual : A.polarized.dual.abelian.scheme ≅ (U.polarized.dual.abelian.pullback f.left).scheme
  abelianGroup : IsMonHom abelian.hom
  dualGroup : IsMonHom dual.hom
  polarization : A.polarized.polarization.isogeny.hom ≫ dual.hom =
    abelian.hom ≫ (Over.pullback f.left).map U.polarized.polarization.isogeny.hom
  poincare : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      ((dual.hom ⊗ₘ abelian.hom).left ≫
        HilbertConstruction.PolarizationData.poincareBaseChangeMap U.polarized.dual f.left)
      (HilbertConstruction.Line.Bundles.LineBundle.classOf U.polarized.dual.poincare) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf A.polarized.dual.poincare
  level : ∀ (Y : Over T.left)
    (c : LocallyConstant Y.left (Multiplicative (Fin (2 * (3 * s)) → ZMod N))),
    (A.polarized.level.hom.app (.op Y) c).val ≫ abelian.hom =
      ((U.polarized.level.pullback f.left).hom.app (.op Y) c).val
  action : ∀ a : NumberField.RingOfIntegers E,
    A.action.map a ≫ abelian.hom =
      abelian.hom ≫ (Over.pullback f.left).map (U.action.map a)

/-- Candidate fine moduli model. Its universal property and geometry
are separate conclusions in ReferenceFamily. -/
structure FinePELModel (P : Datum.RankThreePELDatum E s) (iota : E →+* K) (N : ℕ) where
  space : Over (Spec (.of K))
  universal : PEL.Objects.PELObject P iota N space

namespace FinePELModel

variable (M : FinePELModel P iota N)

/-- The entire fixed-level PEL problem, on all test schemes over K. -/
def IsFine : Prop :=
  ∀ (T : Over (Spec (.of K))) (A : PEL.Objects.PELObject P iota N T),
    ∃! f : T ⟶ M.space, Nonempty (PELPullbackIso M.universal A f)

def complexFiber (κ : K →+* ℂ) : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj M.space

abbrev ComplexPoints (κ : K →+* ℂ) := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (M.complexFiber κ)

abbrev ComplexComponent (κ : K →+* ℂ) := ConnectedComponents (M.ComplexPoints κ)

def ComponentPoints (κ : K →+* ℂ) (C : M.ComplexComponent κ) :=
  {x : M.ComplexPoints κ // ConnectedComponents.mk x = C}

instance componentTopology (κ : K →+* ℂ) (C : M.ComplexComponent κ) :
    TopologicalSpace (M.ComponentPoints κ C) := inferInstanceAs
      (TopologicalSpace {x : M.ComplexPoints κ // ConnectedComponents.mk x = C})

end FinePELModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Models
