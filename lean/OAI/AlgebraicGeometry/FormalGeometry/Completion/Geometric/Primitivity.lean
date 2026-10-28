import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProductAxes
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.ProductAxes

/-! # Primitivity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Primitivity.Construction

noncomputable section

/-! Every actual geometric H¹ class of a proper smooth integral group scheme is primitive. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

/-- Restriction to both identity axes detects a class on the actual geometric product. -/
theorem geometricH1_eq_zero_of_axes (x : Cohomology.Construction.GeometricH1 ℓ (A ⊗ A))
    (hfirst : Endomorphism.Action.Construction.geometricH1Pullback ℓ k (Product.Axes.Construction.groupFirstAxis k A) x = 0)
    (hsecond : Endomorphism.Action.Construction.geometricH1Pullback ℓ k (Product.Axes.Construction.groupSecondAxis k A) x = 0) : x = 0 := by
  have : IsProper (Frobenius.Construction.geometricFiberOver k A).hom :=
    inferInstanceAs (IsProper (pullback.snd A.hom (Frobenius.Construction.algebraicClosureBase k)))
  have : Smooth (Frobenius.Construction.geometricFiberOver k A).hom :=
    inferInstanceAs (Smooth (pullback.snd A.hom (Frobenius.Construction.algebraicClosureBase k)))
  have : GeometricallyIntegral (Frobenius.Construction.geometricFiberOver k A).hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.hom (Frobenius.Construction.algebraicClosureBase k)))
  let j := ProductAxes.Construction.geometricProductIso k A A
  have hy : CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.inv x = 0 := by
    apply ProductAxes.Construction.algebraicEllAdicH1_eq_zero_of_axes (Frobenius.Construction.geometricFiberOver k A).hom
      (Frobenius.Construction.geometricFiberOver k A).hom ℓ
      (ProductAxes.Construction.geometricIdentitySection k A) (ProductAxes.Construction.geometricIdentitySection_hom k A)
      (ProductAxes.Construction.geometricIdentitySection k A) (ProductAxes.Construction.geometricIdentitySection_hom k A)
    · change ((CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ _).comp
        (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.inv)) x = 0
      rw [CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_comp]
      exact (congrArg (fun f => CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ f x)
        (ProductAxes.Construction.geometricFirstAxis_comparison k A)).trans hfirst
    · change ((CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ _).comp
        (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.inv)) x = 0
      rw [CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_comp]
      exact (congrArg (fun f => CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ f x)
        (ProductAxes.Construction.geometricSecondAxis_comparison k A)).trans hsecond
  have hid : (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.hom).comp
      (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.inv) = LinearMap.id := by
    rw [CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_comp, j.hom_inv_id, CohomologyFunctoriality.Construction.algebraicEllAdicH1Pullback_id]
  have h := congrArg (fun f => f x) hid
  change CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.hom (CohomologyPullback.Construction.algebraicEllAdicH1Pullback ℓ j.inv x) = x at h
  rw [hy, map_zero] at h
  exact h.symm

variable [IsCommMonObj A]

/-- The group-law defect on the full actual geometric H¹ is zero. -/
theorem geometricH1GroupLawDefect_eq_zero : GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k A = 0 := by
  apply LinearMap.ext
  intro x
  apply geometricH1_eq_zero_of_axes ℓ k A
  · exact congrArg (fun f => f x) (Product.Axes.Construction.geometricH1GroupLawDefect_firstAxis ℓ k A)
  · exact congrArg (fun f => f x) (Product.Axes.Construction.geometricH1GroupLawDefect_secondAxis ℓ k A)

/-- The previously constructed primitive submodule is the entire actual H¹. -/
theorem primitiveGeometricH1_eq_top : GroupLawCohomology.Construction.PrimitiveGeometricH1 ℓ k A = ⊤ := by
  change LinearMap.ker (GroupLawCohomology.Construction.geometricH1GroupLawDefect ℓ k A) = ⊤
  rw [geometricH1GroupLawDefect_eq_zero, LinearMap.ker_zero]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Primitivity.Construction
