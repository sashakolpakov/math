import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel
import OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny

/-! # Dual Model -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel

/-! Algebraize the integral dual reference lattice and its inclusion.
The resulting finite etale isogeny is constructed from the actual period
maps. Identifying the target with the represented Picard dual remains
a separate assertion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

structure ReferenceDualModel where
  abelian : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  period : (F.dualPeriodData hP).periodTorus ≃ₘ⟮𝓘(ℂ, (F.dualPeriodData hP).space),
    𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel abelian)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints abelian.toOver
  period_add : ∀ u v, period (u + v) = period u * period v

theorem referenceDualModel_nonempty : Nonempty (ReferenceDualModel F hP) := by
  obtain ⟨A, e, he⟩ :=
    RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model_with_group (F.dualPeriodData hP)
  exact ⟨⟨A, e, he⟩⟩

def referenceDualModel : ReferenceDualModel F hP :=
  Classical.choice (referenceDualModel_nonempty F hP)

namespace ReferenceDualModel

variable {F hP} (M : ReferenceDualModel F hP)

theorem dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom = 3 * s := by
  have h := RepresentationTheory.Theta.Geometric.AbelianScheme.abelian_model_dimension (F.dualPeriodData hP) M.abelian M.period
  change Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom =
    Module.finrank ℂ (Fin (3 * Fintype.card (Fin s)) → ℂ) at h
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using h

def abelianScheme : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := M.abelian.toOver
  group := M.abelian.group
  commutative := M.abelian.commutative
  proper := M.abelian.variety.presentation.projective.isProper
  smoothDimension := by
    rw [← M.dimension]
    exact Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension M.abelian.toOver.hom
  connected := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian).connected

end ReferenceDualModel

namespace ReferenceAnalyticFiber

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.latticeTorusMap : F.periodData.periodTorus →+ (F.dualPeriodData hP).periodTorus :=
  RepresentationTheory.Theta.Geometric.Torus.Hom.torusLinearMap F.periodData (F.dualPeriodData hP)
    (LinearMap.id : F.periodData.space →ₗ[ℂ] F.periodData.space)
    (fun _ hv => F.lattice_le_dual hP hv)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.exists_lattice_isogeny (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : ReferenceDualModel F hP) :
    ∃ f : M.abelian.toOver ⟶ D.abelian.toOver,
      IsMonHom f ∧ IsFinite f.left ∧ Etale f.left ∧ Surjective f.left ∧
      ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) = D.period (F.latticeTorusMap hP t) := by
  obtain ⟨n, hn, hL⟩ := F.dualLattice_bounded_denominator hP
  exact RepresentationTheory.Theta.Geometric.Torus.Isogeny.exists_algebraic_torus_isogeny F.periodData (F.dualPeriodData hP)
    LinearMap.id (n • LinearMap.id)
    (fun _ hv => F.lattice_le_dual hP hv)
    (fun v hv => hL ⟨v, hv⟩) n hn (fun _ => rfl) (fun _ => rfl)
    M.abelian D.abelian M.period D.period M.period_add D.period_add

end ReferenceAnalyticFiber

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceAnalyticFiber

/-! The actual reference lattice torus map has the prescribed finite
kernel, with its labels obtained from the original integral form. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

local instance : F.periodData.periodIntegerLattice.toAddSubgroup.Normal := by
  change F.lattice.Normal
  infer_instance

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.periodQuotient_eq_zero (v : F.periodData.space) :
    (QuotientAddGroup.mk v : F.periodData.periodTorus) = 0 ↔
      v ∈ F.periodData.periodIntegerLattice := by
  change (QuotientAddGroup.mk (v : Fiber.ReferenceTangent s) : Fiber.ReferenceTangent s ⧸ F.lattice) = 0 ↔
    v ∈ F.lattice
  exact @QuotientAddGroup.eq_zero_iff (Fiber.ReferenceTangent s) inferInstance F.lattice inferInstance v

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.dualPeriodQuotient_eq_zero (v : F.periodData.space) :
    (QuotientAddGroup.mk v : (F.dualPeriodData hP).periodTorus) = 0 ↔ v ∈ F.dualLattice := by
  change (QuotientAddGroup.mk v : Fiber.ReferenceTangent s ⧸ F.dualLattice.toAddSubgroup) = 0 ↔
    v ∈ F.dualLattice
  exact @QuotientAddGroup.eq_zero_iff (Fiber.ReferenceTangent s) inferInstance
    F.dualLattice.toAddSubgroup inferInstance v

local instance : (F.dualPeriodData hP).periodIntegerLattice.toAddSubgroup.Normal := by
  change F.dualLattice.toAddSubgroup.Normal
  infer_instance

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.latticeKernelLift : F.dualLattice →+ (F.latticeTorusMap hP).ker where
  toFun v := ⟨QuotientAddGroup.mk v.val, (F.dualPeriodQuotient_eq_zero hP v.val).mpr v.property⟩
  map_zero' := Subtype.ext (@QuotientAddGroup.mk_zero (Fiber.ReferenceTangent s)
    inferInstance F.lattice inferInstance)
  map_add' u v := Subtype.ext (@QuotientAddGroup.mk_add (Fiber.ReferenceTangent s)
    inferInstance F.lattice inferInstance u.val v.val)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.latticeKernelLift_surjective : Function.Surjective (F.latticeKernelLift hP) := by
  intro t
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective t.val
  have hzero := t.property
  change F.latticeTorusMap hP t.val = 0 at hzero
  rw [← hv] at hzero
  have hvL : v ∈ F.dualLattice := (F.dualPeriodQuotient_eq_zero hP v).mp hzero
  exact ⟨⟨v, hvL⟩, Subtype.ext hv⟩

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.latticeKernelLift_ker : (F.latticeKernelLift hP).toIntLinearMap.ker =
    (F.latticeDualInclusion hP).range := by
  ext v
  change F.latticeKernelLift hP v = 0 ↔ ∃ u, F.latticeDualInclusion hP u = v
  constructor
  · intro h
    have hz := congrArg Subtype.val h
    have hv : v.val ∈ F.periodData.periodIntegerLattice := (F.periodQuotient_eq_zero v.val).mp hz
    obtain ⟨u, hu⟩ := F.integralLatticeEquiv.surjective ⟨v.val, hv⟩
    refine ⟨u, Subtype.ext ?_⟩
    exact congrArg (fun w : F.periodData.periodIntegerLattice => w.val) hu
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    exact (F.periodQuotient_eq_zero _).mpr (F.integralLatticeEquiv u).property

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.discriminantKernelEquiv : (F.dualLattice ⧸ (F.latticeDualInclusion hP).range) ≃+
    (F.latticeTorusMap hP).ker :=
  ((Submodule.quotEquivOfEq _ _ (F.latticeKernelLift_ker hP).symm).trans
    (LinearMap.quotKerEquivOfSurjective (F.latticeKernelLift hP).toIntLinearMap
      (F.latticeKernelLift_surjective hP))).toAddEquiv

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.latticeKernel_type : Nonempty ((F.latticeTorusMap hP).ker ≃+
    ((∀ i : Fin (3 * s), ZMod (P.polarizationType i)) ×
      (∀ i : Fin (3 * s), ZMod (P.polarizationType i)))) :=
  ⟨(F.discriminantKernelEquiv hP).symm.trans (F.discriminant_type hP).some⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceAnalyticFiber

end

end OAI
