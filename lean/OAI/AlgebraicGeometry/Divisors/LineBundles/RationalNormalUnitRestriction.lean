import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRNeighborhood
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidueEvaluation

/-! # Rational Normal Unit Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.RationalNormalUnitRestriction.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: an actual order-zero rational function is a regular unit near a normal divisor point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem exists_regularUnit_neighborhood_of_order_zero (x : X) (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)] (a : X.functionFieldˣ) (ha : X.ord a.val x = 0) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hxU : x ∈ U) (u : Γ(X, U)ˣ),
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm U u = a := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨U, hU, hxU, _, u, _, hu⟩ := DVRNeighborhood.BundleCycles.rationalFunction_DVR_neighborhood X x hx π hπ a.val a.ne_zero
  refine ⟨U, hU, hxU, u, ?_⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply Units.ext
  change X.germToFunctionField U u.val = a.val
  rw [ha, zpow_zero, mul_one] at hu
  exact hu.symm

end

section

/-! # LineBundleCycles: ordinary restriction of an actual order-zero rational function to its prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]
    (g : X.functionFieldˣ) (hg : X.ord g.val x = 0)

include hx hg in
theorem exists_normalOrderZeroUnit :
    ∃ u : (X.presheaf.stalk x)ˣ, Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u = g := by
  obtain ⟨U, _, hxU, u, hu⟩ := exists_regularUnit_neighborhood_of_order_zero X x hx g hg
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨Units.map (X.presheaf.germ U x hxU).hom.toMonoidHom u, ?_⟩
  apply Units.ext
  change algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU u.val) = g.val
  rw [Scheme.algebraMap_germ_eq_germToFunctionField X hxU u.val]
  exact congrArg (fun v : X.functionFieldˣ => v.val) hu

def normalOrderZeroUnit : (X.presheaf.stalk x)ˣ :=
  (exists_normalOrderZeroUnit X x hx g hg).choose

theorem normalOrderZeroUnit_spec :
    Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom
      (normalOrderZeroUnit X x hx g hg) = g :=
  (exists_normalOrderZeroUnit X x hx g hg).choose_spec

theorem normalOrderZeroUnit_unique (u : (X.presheaf.stalk x)ˣ)
    (hu : Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u = g) :
    u = normalOrderZeroUnit X x hx g hg := by
  apply Units.ext
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  exact congrArg (fun v : X.functionFieldˣ => v.val)
    (hu.trans (normalOrderZeroUnit_spec X x hx g hg).symm)

def normalRationalRestriction : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionFieldˣ :=
  Units.map (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom.toMonoidHom
    (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom (normalOrderZeroUnit X x hx g hg))

theorem normalRationalRestriction_apply : (normalRationalRestriction X x hx g hg).val =
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x
      (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom (normalOrderZeroUnit X x hx g hg)) := rfl

end

/-! # LineBundleCycles: multiplication and actual regular-function evaluation for ordinary rational restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalOrderZeroUnit_mul (g h : X.functionFieldˣ)
    (hg : X.ord g.val x = 0) (hh : X.ord h.val x = 0) (hgh : X.ord (g * h).val x = 0) :
    normalOrderZeroUnit X x hx (g * h) hgh =
      normalOrderZeroUnit X x hx g hg * normalOrderZeroUnit X x hx h hh := by
  symm
  apply normalOrderZeroUnit_unique X x hx (g * h) hgh
  rw [map_mul, normalOrderZeroUnit_spec, normalOrderZeroUnit_spec]

theorem normalRationalRestriction_mul (g h : X.functionFieldˣ)
    (hg : X.ord g.val x = 0) (hh : X.ord h.val x = 0) (hgh : X.ord (g * h).val x = 0) :
    normalRationalRestriction X x hx (g * h) hgh =
      normalRationalRestriction X x hx g hg * normalRationalRestriction X x hx h hh := by
  unfold normalRationalRestriction
  rw [normalOrderZeroUnit_mul X x hx g h hg hh hgh, map_mul]
  exact map_mul (Units.map (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom.toMonoidHom) _ _

theorem normalRationalRestriction_regular (g : X.functionFieldˣ) (hg : X.ord g.val x = 0)
    (a : Γ(X, ⊤)) (ha : IsUnit (X.presheaf.germ ⊤ x (by trivial) a))
    (hga : g.val = RegularDivisor.BundleCycles.globalFunctionFieldElement X a) :
    (normalRationalRestriction X x hx g hg).val =
      RegularDivisor.BundleCycles.globalFunctionFieldElement (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).appTop a) := by
  obtain ⟨u, hu⟩ := ha
  have huf : Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u = g := by
    apply Units.ext
    change algebraMap (X.presheaf.stalk x) X.functionField u.val = g.val
    rw [hu, Scheme.algebraMap_germ_eq_germToFunctionField X (by trivial) a]
    exact hga.symm
  rw [normalRationalRestriction_apply, ← normalOrderZeroUnit_unique X x hx g hg u huf]
  exact Geometric.ResidueRegular.BundleCycles.pointSupportResidueFunction_regular X x a u hu

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.RationalNormalUnitRestriction.BundleCycles
