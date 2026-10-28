import OAI.AlgebraicGeometry.Foundations.Scheme.DifferentialRankLocalization
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Affine Dimension -/

namespace OAI.AlgebraicGeometry.Betti.AffineDimension.Realization

noncomputable section

/-!
# One function-field dimension for the affine charts of an integral scheme

The algebra structures are induced by the actual structure morphism, section
restriction, and germ maps. Their compatibility is proved from the sheaf germ
identity. Consequently standard smooth presentations on different nonempty
affine opens have a common dimension: the rank of differentials of the same
function field over the same base ring.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v w

variable {X Y : Scheme.{u}}

/-- Restriction of the structure morphism on sections to an arbitrary source open. -/
def sectionBaseMap (f : X ⟶ Y) (U : X.Opens) : Γ(Y, ⊤) ⟶ Γ(X, U) :=
  f.appLE ⊤ U le_top

/-- The actual base-ring algebra structure on the sections of a source open. -/
abbrev sectionBaseAlgebra (f : X ⟶ Y) (U : X.Opens) :
    Algebra Γ(Y, ⊤) Γ(X, U) :=
  (sectionBaseMap f U).hom.toAlgebra

variable [IrreducibleSpace X]

/-- The structure morphism followed by the germ at the generic point. -/
def functionFieldBaseMap (f : X ⟶ Y) : Γ(Y, ⊤) ⟶ X.functionField :=
  f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) (by trivial)

/-- The actual base-ring algebra structure on the function field. -/
abbrev functionFieldBaseAlgebra (f : X ⟶ Y) :
    Algebra Γ(Y, ⊤) X.functionField :=
  (functionFieldBaseMap f).hom.toAlgebra

/-- Restricting to a nonempty open does not change the germ of a base section. -/
theorem sectionBaseMap_germ (f : X ⟶ Y) (U : X.Opens) [Nonempty U] :
    sectionBaseMap f U ≫ X.germToFunctionField U = functionFieldBaseMap f := by
  dsimp only [sectionBaseMap, functionFieldBaseMap, Scheme.Hom.appLE,
    Scheme.germToFunctionField]
  rw [Category.assoc, TopCat.Presheaf.germ_res]
  congr 1

/-- The source-open and function-field algebra structures form the required
scalar tower; this is proved, rather than included as an assumption. -/
theorem functionFieldBase_isScalarTower (f : X ⟶ Y) (U : X.Opens) [Nonempty U] :
    letI := sectionBaseAlgebra f U
    letI := functionFieldBaseAlgebra f
    IsScalarTower Γ(Y, ⊤) Γ(X, U) X.functionField := by
  let := sectionBaseAlgebra f U
  let := functionFieldBaseAlgebra f
  apply IsScalarTower.of_algebraMap_eq'
  change (functionFieldBaseMap f).hom =
    (X.germToFunctionField U).hom.comp (sectionBaseMap f U).hom
  exact congrArg CommRingCat.Hom.hom (sectionBaseMap_germ f U).symm

variable [IsIntegral X]

/-- The common dimension recorded in the differentials of the actual function
field, with its structure-morphism algebra structure. -/
def functionFieldDifferentialDimension (f : X ⟶ Y) : ℕ :=
  letI := functionFieldBaseAlgebra f
  Module.finrank X.functionField Ω[X.functionField⁄Γ(Y, ⊤)]

/-- A genuine standard smooth affine presentation has the dimension of the
same function-field differential space, independently of the chosen open. -/
theorem affinePresentation_dimension (f : X ⟶ Y) (U : X.Opens) [Nonempty U]
    (hU : IsAffineOpen U) (ι : Type v) (σ : Type w) [Finite ι] [Finite σ] :
    letI := sectionBaseAlgebra f U
    ∀ P : Algebra.SubmersivePresentation Γ(Y, ⊤) Γ(X, U) ι σ,
      P.dimension = functionFieldDifferentialDimension f := by
  let := sectionBaseAlgebra f U
  let := functionFieldBaseAlgebra f
  let := functionFieldBase_isScalarTower f U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  intro P
  exact Foundations.Scheme.DifferentialRankLocalization.Algebraic.submersive_dimension_eq_fraction_differential_finrank
    (T := X.functionField) P

end

end OAI.AlgebraicGeometry.Betti.AffineDimension.Realization
