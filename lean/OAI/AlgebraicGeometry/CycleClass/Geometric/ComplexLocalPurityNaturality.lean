import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLinearLocalCohomology

/-! # Complex Local Purity Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality

noncomputable section

/-!
# Coordinate independence of the normalized complex local class

Actual complex-linear coordinates induce the same pullback on local
cohomology because their transition automorphism is homotopic to the
identity as a map of the punctured pair. Consequently the normalized
finite-dimensional complex local class is independent of coordinates and
is natural under complex-linear equivalences. The final formula records
the required transport of cohomological degree explicitly.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Cycles

variable {E F G : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Actual local cohomology pullback is contravariant under composition
of continuous complex-linear equivalences. -/
theorem complexLinearLocalCohomologyIso_trans_hom
    (e : E ≃L[ℂ] F) (f : F ≃L[ℂ] G) (n : ℕ) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (e.trans f) n).hom =
      (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso f n).hom ≫
        (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e n).hom := by
  exact RelativeCochainFunctoriality.Cohomology.relativeSingularCohomologyMap_of_comp (ModuleCat.of ℚ ℚ)
    (FiniteComplexLocalPurity.Cycles.complexLinearTopIso e).hom (FiniteComplexLocalPurity.Cycles.complexLinearTopIso f).hom
    (FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture e) (FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture f) n

/-- Two actual complex-linear coordinate systems have identical induced
pullback maps on local cohomology in every degree. -/
theorem complexLinearLocalCohomologyIso_hom_eq_of_coordinates {p : ℕ}
    (e f : E ≃L[ℂ] (Fin p → ℂ)) (n : ℕ) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e n).hom =
      (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso f n).hom := by
  have hcoord : e.trans (e.symm.trans f) = f := by
    apply ContinuousLinearEquiv.ext
    funext x
    exact congrArg f (e.symm_apply_apply x)
  have hid : (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso (e.symm.trans f) n).hom = 𝟙 _ :=
    ComplexLinearLocalCohomology.Cycles.complexLinearLocalCohomologyMap_eq_id (e.symm.trans f)
      (FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture (e.symm.trans f)) n
  have h := complexLinearLocalCohomologyIso_trans_hom e (e.symm.trans f) n
  rw [hcoord, hid, Category.id_comp] at h
  exact h.symm

/-- The normalized local class transported by an actual coordinate map. -/
def complexCoordinateLocalClass {p : ℕ} (e : E ≃L[ℂ] (Fin p → ℂ)) :
    FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E (2 * p) :=
  (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * p)).hom
    ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1)

/-- The transported normalized class does not depend on its coordinates. -/
theorem complexCoordinateLocalClass_eq {p : ℕ}
    (e f : E ≃L[ℂ] (Fin p → ℂ)) :
    complexCoordinateLocalClass e = complexCoordinateLocalClass f := by
  exact ConcreteCategory.congr_hom
    (complexLinearLocalCohomologyIso_hom_eq_of_coordinates e f (2 * p))
      ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1)

/-- Pullback preserves the coordinate-normalized class for any actual
complex-linear equivalence and any coordinates in the same dimension. -/
theorem complexCoordinateLocalClass_naturality {p : ℕ}
    (e : E ≃L[ℂ] F) (cE : E ≃L[ℂ] (Fin p → ℂ)) (cF : F ≃L[ℂ] (Fin p → ℂ)) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * p)).hom (complexCoordinateLocalClass cF) =
      complexCoordinateLocalClass cE := by
  have h := ConcreteCategory.congr_hom
    (complexLinearLocalCohomologyIso_trans_hom e cF (2 * p))
      ((RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso p).inv 1)
  exact h.symm.trans (complexCoordinateLocalClass_eq (e.trans cF) cE)

/-- Reindexing the coordinate dimension transports the actual class by
the corresponding equality of local cohomology objects. -/
theorem complexCoordinateLocalClass_cast {p q : ℕ} (h : p = q)
    (e : E ≃L[ℂ] (Fin p → ℂ)) :
    (eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E (2 * n)) h))
        (complexCoordinateLocalClass e) =
      complexCoordinateLocalClass
        (cast (congrArg (fun n => E ≃L[ℂ] (Fin n → ℂ)) h) e) := by
  subst q
  rfl

variable (E) [FiniteDimensional ℂ E]

/-- The previously constructed local class is exactly the coordinate
normalization for its chosen actual coordinates. -/
theorem finiteComplexLocalClass_eq_coordinate :
    FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass E = complexCoordinateLocalClass (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E) :=
  rfl

/-- Any actual complex coordinates in the full dimension give the
canonical local class. -/
theorem finiteComplexLocalClass_eq_of_coordinates
    (e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ)) :
    FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass E = complexCoordinateLocalClass e := by
  exact (finiteComplexLocalClass_eq_coordinate E).trans
    (complexCoordinateLocalClass_eq (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E) e)

variable {E} [FiniteDimensional ℂ F]

/-- The normalized local class is natural under actual complex-linear
equivalences, with the equality of complex dimensions transported explicitly. -/
theorem finiteComplexLocalClass_naturality (e : E ≃L[ℂ] F) :
    (FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso e (2 * Module.finrank ℂ F)).hom
        (FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass F) =
      (eqToHom (congrArg (fun n => FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology E (2 * n))
        e.toLinearEquiv.finrank_eq)) (FiniteComplexLocalPurity.Cycles.finiteComplexLocalClass E) := by
  rw [finiteComplexLocalClass_eq_coordinate F, finiteComplexLocalClass_eq_coordinate E,
    complexCoordinateLocalClass_cast e.toLinearEquiv.finrank_eq (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E)]
  exact complexCoordinateLocalClass_naturality e
    (cast (congrArg (fun n => E ≃L[ℂ] (Fin n → ℂ)) e.toLinearEquiv.finrank_eq)
      (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates E)) (FiniteComplexLocalPurity.Cycles.finiteComplexCoordinates F)

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality
