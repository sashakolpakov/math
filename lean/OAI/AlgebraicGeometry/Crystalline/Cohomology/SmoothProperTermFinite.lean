import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperOrdinaryFormFiniteness
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ProperCoherentAdd
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ConnectiveHypercohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor

/-! # Smooth Proper Term Finite -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothProperTermFinite.SmoothProperDeRhamFiniteness

noncomputable section

/-! # Finiteness of the original smooth proper de Rham hypercohomology -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [CharZero k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves k X) := HasExt.standard _

theorem term_finite (n q : ℕ) :
    Module.Finite k (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X)
      ((DeRhamGlobalId.DeRhamGlobal.sheafComplex k X).X n) q) := by
  let M := ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.term k X n
  let : M.IsQuasicoherent := ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.quasicoherent k X n
  let : M.IsFiniteType := ProperOrdinaryFormFiniteness.SmoothProperOrdinaryFormFiniteness.finiteType k X n
  let : Module.Finite k (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X)
      ((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.functor k X).obj M) q) :=
    ProperCoherentAdd.ProperCoherentCoefficientExt.finite k X M q
  let e : Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X)
      ((NumberTheory.PadicHodge.IntegralComparison.AlgebraSheafScalars.functor k X).obj M) q ≃ₗ[k]
        Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X) ((DeRhamGlobalId.DeRhamGlobal.sheafComplex k X).X n) q :=
    ((NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor k (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X) q).mapIso
      (OrdinaryFormSheaf.OrdinaryFormSheafComparison.iso k X n)).toLinearEquiv
  exact Module.Finite.equiv e

theorem finite (n : ℕ) : Module.Finite k (DeRhamGlobalId.DeRhamGlobal.cohomology k X n) :=
  ConnectiveHypercohomology.ConnectiveHypercohomologyFiniteness.finite k (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf k X)
    (DeRhamGlobalId.DeRhamGlobal.sheafComplex k X) n (fun r _ => term_finite k X r (n - r))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothProperTermFinite.SmoothProperDeRhamFiniteness
