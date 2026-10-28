import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingLoop
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.Winding

/-! # Winding Normalization -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary

/-!
# ThomClass: logarithmic winding and the fixed normal-class normalization

The actual singular logarithm cocycle gives a nonzero winding generator.
Transporting it to the normal-coordinate complex line and applying the
connecting map determines a nonzero rational coefficient relative to the
project's fixed oriented normal class. This coefficient is constructed and
proved nonzero; it is not an assumed comparison of algebraic cycle classes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- The literal coordinate identification of the two punctured complex-line models. -/
def puncturedLineCoordinateHomeomorph : PrincipalBoundary.Constructions.puncturedComplexLine ≃ₜ DivisorClass.Chern.WindingLoop.puncturedPlane where
  toFun z := ⟨z.val 0, fun h => z.property (by
    apply Set.mem_singleton_iff.mpr
    funext i
    exact (congrArg z.val (Subsingleton.elim i 0)).trans h)⟩
  invFun z := ⟨fun _ => z.val, fun h => z.property (congrFun (Set.mem_singleton_iff.mp h) 0)⟩
  left_inv z := Subtype.ext (funext fun i => congrArg z.val (Subsingleton.elim 0 i))
  right_inv _ := rfl
  continuous_toFun := ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_pi fun _ => continuous_subtype_val).subtype_mk _

def puncturedLineCoordinateIso : TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine ≅ DivisorClass.Chern.WindingLoop.puncturedPlane :=
  TopCat.isoOfHomeo puncturedLineCoordinateHomeomorph

/-- The explicit nonzero logarithmic winding class in the normal-coordinate model. -/
def logarithmicLineWinding :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) 1 :=
  AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) puncturedLineCoordinateIso.hom 1
    (DivisorClass.Chern.WindingSingular.singularWindingClass DivisorClass.Chern.WindingLoop.puncturedPlane DivisorClass.Chern.WindingLoop.puncturedCoordinate DivisorClass.Chern.WindingLoop.puncturedCoordinate_ne_zero)

theorem logarithmicLineWinding_ne_zero : logarithmicLineWinding ≠ 0 := by
  let e := (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of ℚ ℚ) 1).mapIso puncturedLineCoordinateIso.op
  intro h
  apply DivisorClass.Chern.WindingLoop.singularWindingClass_punctured_ne_zero
  apply e.toLinearEquiv.injective
  exact h.trans e.toLinearEquiv.map_zero.symm

/-- The actual logarithmic residue in the relative cohomology of the normal line. -/
def logarithmicLineResidue :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) PrincipalBoundary.Constructions.normalComplexLine PrincipalBoundary.Constructions.puncturedComplexLine 2 :=
  PrincipalBoundary.Constructions.lineConnectingIso.hom logarithmicLineWinding

theorem logarithmicLineResidue_ne_zero : logarithmicLineResidue ≠ 0 := by
  intro h
  apply logarithmicLineWinding_ne_zero
  apply PrincipalBoundary.Constructions.lineConnectingIso.toLinearEquiv.injective
  exact h.trans PrincipalBoundary.Constructions.lineConnectingIso.toLinearEquiv.map_zero.symm

/-- The rational normalization coefficient is computed from the fixed local cohomology isomorphism. -/
def logarithmicNormalCoefficient : ℚ :=
  Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1 logarithmicLineResidue

theorem logarithmicNormalCoefficient_ne_zero : logarithmicNormalCoefficient ≠ 0 := by
  intro h
  apply logarithmicLineResidue_ne_zero
  apply (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1).injective
  exact h.trans (map_zero (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1)).symm

theorem logarithmicLineResidue_eq_normal :
    logarithmicLineResidue = logarithmicNormalCoefficient • Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1 := by
  apply (Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1).injective
  rw [map_smul, Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_normalization]
  exact (mul_one logarithmicNormalCoefficient).symm

/-- The same nonzero normalization relates the actual winding classes. -/
theorem logarithmicLineWinding_eq_normalized :
    logarithmicLineWinding = logarithmicNormalCoefficient • PrincipalBoundary.Constructions.lineWindingClass := by
  apply PrincipalBoundary.Constructions.lineConnectingIso.toLinearEquiv.injective
  change logarithmicLineResidue = PrincipalBoundary.Constructions.lineConnectingIso.hom (_ • PrincipalBoundary.Constructions.lineWindingClass)
  rw [map_smul]
  exact logarithmicLineResidue_eq_normal.trans
    (congrArg (fun a => logarithmicNormalCoefficient • a) PrincipalBoundary.Constructions.lineWindingClass_boundary.symm)

/-- A punctured-line map expressed as an actual nonvanishing complex-valued function. -/
def puncturedMapCoordinate {X : TopCat} (g : X ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) : C(X, ℂ) :=
  DivisorClass.Chern.WindingLoop.puncturedCoordinate.comp (g ≫ puncturedLineCoordinateIso.hom).hom

theorem puncturedMapCoordinate_ne_zero {X : TopCat} (g : X ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine)
    (x : X) : puncturedMapCoordinate g x ≠ 0 :=
  DivisorClass.Chern.WindingLoop.puncturedCoordinate_ne_zero _

/-- The actual logarithm cocycle of a function equals the fixed nonzero
coefficient times ThomClass's normalized winding pullback. -/
theorem singularWindingClass_eq_normalized {X : TopCat}
    (g : X ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) :
    DivisorClass.Chern.WindingSingular.singularWindingClass X (puncturedMapCoordinate g) (puncturedMapCoordinate_ne_zero g) =
      logarithmicNormalCoefficient •
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 1 PrincipalBoundary.Constructions.lineWindingClass := by
  have h := DivisorClass.Chern.WindingSingular.singularWindingClass_naturality (g ≫ puncturedLineCoordinateIso.hom)
    DivisorClass.Chern.WindingLoop.puncturedCoordinate DivisorClass.Chern.WindingLoop.puncturedCoordinate_ne_zero
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp] at h
  change AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 1 logarithmicLineWinding =
    DivisorClass.Chern.WindingSingular.singularWindingClass X (puncturedMapCoordinate g) (puncturedMapCoordinate_ne_zero g) at h
  rw [logarithmicLineWinding_eq_normalized, map_smul] at h
  exact h.symm

/-- Applying the genuine connecting map gives the corresponding supported comparison. -/
theorem supportedWindingClass_eq_normalized {X : TopCat} (A : Set X)
    (g : TopCat.of A ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) :
    DivisorClass.Chern.Supported.Winding.supportedWindingClass X A (puncturedMapCoordinate g) (puncturedMapCoordinate_ne_zero g) =
      logarithmicNormalCoefficient • AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A 1
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 1 PrincipalBoundary.Constructions.lineWindingClass) := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A 1
    (DivisorClass.Chern.WindingSingular.singularWindingClass (TopCat.of A) _ _) = _
  rw [singularWindingClass_eq_normalized, map_smul]

end AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.PrincipalBoundary

namespace AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

/-! Algebraic-looking local equations have their actual integer winding
multiplicity, and multiplication by an extending unit does not change it. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def normalizedWindingBoundary (X : TopCat.{0}) (A : Set X)
    (g : TopCat.of A ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A 1
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 1 PrincipalBoundary.Constructions.lineWindingClass)

theorem normalizedWindingBoundary_unit_power (X : TopCat.{0}) (A : Set X)
    (g f : TopCat.of A ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine)
    (u : C(X, ℂ)) (hu : ∀ x, u x ≠ 0) (m : ℤ)
    (hfg : ∀ x, PrincipalBoundary.puncturedMapCoordinate f x = PrincipalBoundary.puncturedMapCoordinate g x ^ m * u x.val) :
    normalizedWindingBoundary X A f = m • normalizedWindingBoundary X A g := by
  have h := DivisorClass.Chern.Supported.Winding.supportedWindingClass_unit_power X A (PrincipalBoundary.puncturedMapCoordinate g) (PrincipalBoundary.puncturedMapCoordinate f)
    (PrincipalBoundary.puncturedMapCoordinate_ne_zero g) (PrincipalBoundary.puncturedMapCoordinate_ne_zero f) u hu m hfg
  rw [PrincipalBoundary.supportedWindingClass_eq_normalized, PrincipalBoundary.supportedWindingClass_eq_normalized] at h
  apply smul_right_injective _ PrincipalBoundary.logarithmicNormalCoefficient_ne_zero
  exact h.trans (smul_comm m PrincipalBoundary.logarithmicNormalCoefficient _)

theorem normalizedWindingBoundary_absolute_zero (X : TopCat.{0}) (A : Set X)
    (g : TopCat.of A ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X A 2 (normalizedWindingBoundary X A g) = 0 :=
  ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_inclusion (ModuleCat.of ℚ ℚ) X A 1)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 1 PrincipalBoundary.Constructions.lineWindingClass)

theorem normalizedWindingBoundary_equation {X : TopCat.{0}} (A : Set X)
    (g : X ⟶ PrincipalBoundary.Constructions.normalComplexLine) (hg : Set.MapsTo g A PrincipalBoundary.Constructions.puncturedComplexLine) :
    normalizedWindingBoundary X A (Geometric.LocalHomology.Cycles.subspaceMap g hg) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_naturality (ModuleCat.of ℚ ℚ) g hg 1) PrincipalBoundary.Constructions.lineWindingClass
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg 2
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) PrincipalBoundary.Constructions.normalComplexLine PrincipalBoundary.Constructions.puncturedComplexLine 1 PrincipalBoundary.Constructions.lineWindingClass) =
      normalizedWindingBoundary X A (Geometric.LocalHomology.Cycles.subspaceMap g hg) at h
  rw [PrincipalBoundary.Constructions.lineWindingClass_boundary] at h
  exact h.symm

end AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

namespace AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.BoundaryNaturality

/-! Naturality of the normalized winding boundary for actual maps of
pairs, including restriction of a function to a larger closed support. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.Multiplicity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem normalizedWindingBoundary_naturality {X Y : TopCat.{0}}
    (A : Set X) (B : Set Y) (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (g : TopCat.of B ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2
      (Multiplicity.normalizedWindingBoundary Y B g) =
      Multiplicity.normalizedWindingBoundary X A (Geometric.LocalHomology.Cycles.subspaceMap f hf ≫ g) := by
  have hn := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting_naturality (ModuleCat.of ℚ ℚ) f hf 1)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 1 PrincipalBoundary.Constructions.lineWindingClass)
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp (ModuleCat.of ℚ ℚ) (Geometric.LocalHomology.Cycles.subspaceMap f hf) g 1)
    PrincipalBoundary.Constructions.lineWindingClass
  exact hn.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting (ModuleCat.of ℚ ℚ) X A 1) hc.symm)

theorem equation_eq_boundary_restriction {X : TopCat.{0}} (A B : Set X)
    (hAB : A ⊆ B) (f : X ⟶ PrincipalBoundary.Constructions.normalComplexLine)
    (hf : Set.MapsTo f A PrincipalBoundary.Constructions.puncturedComplexLine)
    (g : TopCat.of B ⟶ TopCat.of PrincipalBoundary.Constructions.puncturedComplexLine)
    (hfg : ∀ x : A, f x.val 0 = (g ⟨x.val, hAB x.property⟩).val 0) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2
      (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) hAB 2
      (Multiplicity.normalizedWindingBoundary X B g) := by
  have hm : Geometric.LocalHomology.Cycles.subspaceMap (𝟙 X) (A := A) (B := B) hAB ≫ g = Geometric.LocalHomology.Cycles.subspaceMap f hf := by
    ext x i
    fin_cases i
    exact (hfg x).symm
  rw [normalizedWindingBoundary_naturality, hm, Multiplicity.normalizedWindingBoundary_equation]

end AlgebraicGeometry.CycleClass.Thom.WindingNormalization.Constructions.BoundaryNaturality

end

end OAI
