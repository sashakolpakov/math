import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.Flat.Basic

/-! # Intrinsic Scalar Extension Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact

noncomputable section

/-! # Flatness makes the native scalar-extension functor exact -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor R S

theorem map_exact (C : ShortComplex (ModuleCat.{u} R)) (hC : C.Exact) :
    (C.map P).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  change Function.Exact (C.f.hom.baseChange S) (C.g.hom.baseChange S)
  exact Module.Flat.lTensor_exact S hC

instance finiteLimits : PreservesFiniteLimits P := by
  have h : PreservesFiniteLimits P ∧ PreservesFiniteColimits P :=
    ((Functor.exact_tfae P).out 2 4).mp (map_exact R S)
  exact h.1

instance finiteColimits : PreservesFiniteColimits P := by
  have h : PreservesFiniteLimits P ∧ PreservesFiniteColimits P :=
    ((Functor.exact_tfae P).out 2 4).mp (map_exact R S)
  exact h.2

instance preservesHomology : (P).PreservesHomology := Functor.preservesHomologyOfExact _

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact
