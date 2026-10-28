import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalNormalUnitRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Rational Restriction Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionNaturality.BundleCycles

noncomputable section

/-! # LineBundleCycles: ordinary rational restriction commutes with the actual morphism-induced residue and support maps -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) (x : X)
    (hx : coheight x = 1) (hy : coheight (f x) = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegrallyClosed (Y.presheaf.stalk (f x))]
    (g : Y.functionFieldˣ) (hg : Y.ord g.val (f x) = 0)
    (hg' : X.ord (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom g).val x = 0)

theorem normalOrderZeroUnit_morphism :
    RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit X x hx (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom g) hg' =
      Units.map (f.stalkMap x).hom.toMonoidHom (RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit Y (f x) hy g hg) := by
  symm
  apply RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit_unique X x hx _ hg'
  apply Units.ext
  have hu := congrArg (fun v : Y.functionFieldˣ => Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη v.val)
    (RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit_spec Y (f x) hy g hg)
  change Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη
    (algebraMap (Y.presheaf.stalk (f x)) Y.functionField (RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit Y (f x) hy g hg).val) = _ at hu
  rw [RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x] at hu
  exact hu

theorem normalRationalRestriction_morphism :
    Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction Y (f x) hy g hg).val =
      (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx
        (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom g) hg').val := by
  let u := RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit Y (f x) hy g hg
  have hr := ConcreteCategory.congr_hom (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap_residue f x)
    (Y.residue (f x) u.val)
  have hs := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap f x) u.val
  have he : Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction Y (f x) hy g hg).val =
      (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom (X.residue x (f.stalkMap x u.val)) :=
    hr.trans (congrArg (fun z : X.residueField x => (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom z) hs)
  exact he.trans (congrArg (fun v : (X.presheaf.stalk x)ˣ =>
    (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom (X.residue x v.val))
    (normalOrderZeroUnit_morphism f hη x hx hy g hg hg').symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionNaturality.BundleCycles
