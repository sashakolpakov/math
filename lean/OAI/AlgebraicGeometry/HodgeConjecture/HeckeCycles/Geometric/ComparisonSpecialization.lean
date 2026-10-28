import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison
import OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry

/-! # Comparison Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM

noncomputable section

/-! Construct a single specialization ring map for GeometricComparison's actual model.
Its generic identification and the proved Neron extension determine the
map; an extending endomorphism specializes by its given integral extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model K q jq)

def integralGroup : CommGrp (Over (Spec (.of ℤ_[q]))) := CommGrp.mk A.integral.scheme
def varietyGroup : CommGrp (Over (Spec (.of K))) := CommGrp.mk A.variety.scheme

instance integralGroup_smooth : Smooth (integralGroup A).X.hom :=
  inferInstanceAs (Smooth A.integral.scheme.hom)

instance integralGroup_proper : IsProper (integralGroup A).X.hom :=
  inferInstanceAs (IsProper A.integral.scheme.hom)

instance integralGroup_connected : GeometricallyConnected (integralGroup A).X.hom :=
  inferInstanceAs (GeometricallyConnected A.integral.scheme.hom)

def localGroup : CommGrp (Over (Spec (.of ℚ_[q]))) :=
  GroupBaseChange.CM.changedGroup (integralGroup A) (NeronSpecialization.CM.genericBase (R := ℤ_[q]) (K := ℚ_[q]))

def completedVarietyGroup : CommGrp (Over (Spec (.of ℚ_[q]))) :=
  GroupBaseChange.CM.changedGroup (varietyGroup A) (Spec.map (CommRingCat.ofHom jq))

def genericIdentification : (localGroup A).X ≅ (completedVarietyGroup A).X := A.genericIso

theorem genericIdentification_group : IsMonHom (genericIdentification A).hom := A.genericIso_group

theorem genericIdentification_inv_group : IsMonHom (genericIdentification A).symm.hom := by
  let : IsMonHom A.genericIso.hom := A.genericIso_group
  exact inferInstanceAs (IsMonHom A.genericIso.inv)

def completedEnd : AbelianScheme.TateComparison.End.IntegralEnd (varietyGroup A).X →+* AbelianScheme.TateComparison.End.IntegralEnd (localGroup A).X := by
  let : IsMonHom (genericIdentification A).symm.hom := genericIdentification_inv_group A
  exact (EndTransportCM.CM.transport (genericIdentification A).symm).toRingHom.comp
    (AbelianScheme.TateComparison.BaseChange.endBaseChange (varietyGroup A).X (Spec.map (CommRingCat.ofHom jq)))

def specializeEnd : FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.variety.scheme →+* FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme :=
  (EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme).toRingHom.comp
    ((NeronSpecialization.CM.specialization (K := ℚ_[q]) (integralGroup A)
      (PadicInt.toZMod : ℤ_[q] →+* ZMod q)).comp
      ((completedEnd A).comp (EndomorphismComparison.CM.integralEquiv A.variety.scheme).symm.toRingHom))

theorem completedEnd_extending (f : A.ExtendingEndomorphism) :
    completedEnd A ((EndomorphismComparison.CM.integralEquiv A.variety.scheme).symm f.generic) =
      NeronSpecialization.CM.genericRestriction (K := ℚ_[q]) (integralGroup A)
        ((EndomorphismComparison.CM.integralEquiv A.integral.scheme).symm f.integral) := by
  let : IsMonHom (genericIdentification A).symm.hom := genericIdentification_inv_group A
  let fg : AbelianScheme.TateComparison.End.IntegralEnd (varietyGroup A).X := (EndomorphismComparison.CM.integralEquiv A.variety.scheme).symm f.generic
  let fi : AbelianScheme.TateComparison.End.IntegralEnd (integralGroup A).X := (EndomorphismComparison.CM.integralEquiv A.integral.scheme).symm f.integral
  let fc : AbelianScheme.TateComparison.End.IntegralEnd (completedVarietyGroup A).X :=
    AbelianScheme.TateComparison.BaseChange.endBaseChange (varietyGroup A).X (Spec.map (CommRingCat.ofHom jq)) fg
  let fl : AbelianScheme.TateComparison.End.IntegralEnd (localGroup A).X :=
    NeronSpecialization.CM.genericRestriction (K := ℚ_[q]) (integralGroup A) fi
  have hc : AbelianScheme.TateComparison.End.endSchemeMap (completedVarietyGroup A).X fc =
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map f.generic.toMul.hom.hom :=
    (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap (varietyGroup A).X (Spec.map (CommRingCat.ofHom jq)) fg).trans
      (congrArg (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map
        (AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap A.variety.scheme f.generic.toMul.hom.hom))
  have hi : AbelianScheme.TateComparison.End.endSchemeMap (localGroup A).X fl =
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map f.integral.toMul.hom.hom :=
    (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap (integralGroup A).X (NeronSpecialization.CM.genericBase (R := ℤ_[q]) (K := ℚ_[q])) fi).trans
      (congrArg (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map
        (AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap A.integral.scheme f.integral.toMul.hom.hom))
  have hw : A.genericIso.hom ≫
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map f.generic.toMul.hom.hom ≫ A.genericIso.inv =
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))).map
        f.integral.toMul.hom.hom := by
    let u := A.localEndomorphism f
    let v : (A.variety.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme ⟶
        (A.variety.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).scheme :=
      (Over.pullback (NumberTheory.PadicHodge.GeometricComparison.Geometry.scalarBaseMap jq)).map f.generic.toMul.hom.hom
    have hc : u ≫ A.genericIso.hom = A.genericIso.hom ≫ v := f.compatible
    exact (Category.assoc A.genericIso.hom v A.genericIso.inv).symm.trans
      ((congrArg (· ≫ A.genericIso.inv) hc).symm.trans
        ((Category.assoc u A.genericIso.hom A.genericIso.inv).trans
          ((congrArg (u ≫ ·) A.genericIso.hom_inv_id).trans (Category.comp_id u))))
  apply AbelianScheme.TateComparison.End.endSchemeMap_injective (localGroup A).X
  exact (EndTransportCM.CM.transport_schemeMap (genericIdentification A).symm fc).trans
    ((congrArg (fun g => A.genericIso.hom ≫ g ≫ A.genericIso.inv) hc).trans
      (hw.trans hi.symm))

theorem specializeEnd_extending (f : A.ExtendingEndomorphism) :
    (specializeEnd A f.generic).toMul.hom.hom = A.specialEndomorphism f := by
  let : GrpObj A.specialFiber.scheme := A.specialFiber.group
  let : IsCommMonObj A.specialFiber.scheme := A.specialFiber.commutative
  let fi : AbelianScheme.TateComparison.End.IntegralEnd (integralGroup A).X := (EndomorphismComparison.CM.integralEquiv A.integral.scheme).symm f.integral
  have h := congrArg
    (NeronSpecialization.CM.specialization (K := ℚ_[q]) (integralGroup A)
      (PadicInt.toZMod : ℤ_[q] →+* ZMod q)) (completedEnd_extending A f)
  have h' := h.trans (NeronSpecialization.CM.specialize_restriction (K := ℚ_[q]) (integralGroup A)
    (PadicInt.toZMod : ℤ_[q] →+* ZMod q) fi)
  have hs := congrArg
    (fun x => (EndomorphismComparison.CM.integralEquiv A.specialFiber.scheme x).toMul.hom.hom) h'
  let fs : AbelianScheme.TateComparison.End.IntegralEnd A.specialFiber.scheme :=
    AbelianScheme.TateComparison.BaseChange.endBaseChange A.integral.scheme
      (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))
      ((EndomorphismComparison.CM.integralEquiv A.integral.scheme).symm f.integral)
  change (specializeEnd A f.generic).toMul.hom.hom =
    AbelianScheme.TateComparison.End.endSchemeMap A.specialFiber.scheme fs at hs
  exact hs.trans ((AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap A.integral.scheme _ _).trans
    (congrArg (Over.pullback
      (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[q] →+* ZMod q)))).map
      (AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap A.integral.scheme f.integral.toMul.hom.hom)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ComparisonSpecialization.CM
