import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.MarkedLevel
import OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelLabels

/-! # Isogeny Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel

noncomputable section

/-! The algebraized reference lattice inclusion has the prescribed
kernel over every geometric field, using its actual finite etale kernel
scheme and the exact period comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

def _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.DualModel.ReferenceDualModel.periodAddEquiv (D : DualModel.ReferenceDualModel F hP) :
    (F.dualPeriodData hP).periodTorus ≃+
      Additive (D.abelianScheme.Points (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase)) where
  toFun t := Additive.ofMul (D.period t)
  invFun p := D.period.symm p.toMul
  left_inv := D.period.symm_apply_apply
  right_inv := D.period.apply_symm_apply
  map_add' := D.period_add

structure ReferenceLatticeIsogeny (M : AlgebraicModel.ReferenceAlgebraicModel F hP) (D : DualModel.ReferenceDualModel F hP) where
  isogeny : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny M.abelianScheme D.abelianScheme
  etale : Etale isogeny.hom.left
  period_eq : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map isogeny.hom (M.period t) =
    D.period (F.latticeTorusMap hP t)

attribute [instance] ReferenceLatticeIsogeny.etale

theorem referenceLatticeIsogeny_nonempty (M : AlgebraicModel.ReferenceAlgebraicModel F hP)
    (D : DualModel.ReferenceDualModel F hP) : Nonempty (ReferenceLatticeIsogeny M D) := by
  obtain ⟨f, hf, hfinite, he, hsurj, hp⟩ := F.exists_lattice_isogeny hP M D
  let : IsMonHom f := hf
  let : Etale f.left := he
  let p : HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny M.abelianScheme D.abelianScheme :=
    ⟨f, hf, hfinite, (Etale.iff_flat_and_formallyUnramified.mp he).1, hsurj⟩
  exact ⟨⟨p, he, hp⟩⟩

namespace ReferenceLatticeIsogeny

variable {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    (p : ReferenceLatticeIsogeny M D)

def complexKernelEquiv : Multiplicative (F.latticeTorusMap hP).ker ≃*
    p.isogeny.kernelAt (ConstantSectionsOn.ConstantSections.baseTest Foundations.Scheme.ProjectiveSpace.complexBase) where
  toFun t := ⟨M.period t.toAdd.val, by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom (M.period t.toAdd.val) = 1
    rw [p.period_eq, show F.latticeTorusMap hP t.toAdd.val = 0 from t.toAdd.property]
    exact congrArg Additive.toMul D.periodAddEquiv.map_zero⟩
  invFun a := Multiplicative.ofAdd ⟨M.period.symm a.val, by
    apply D.period.injective
    exact (p.period_eq _).symm.trans
      ((congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.isogeny.hom) (M.period.apply_symm_apply a.val)).trans
        (a.property.trans (congrArg Additive.toMul D.periodAddEquiv.map_zero).symm))⟩
  left_inv t := by
    apply congrArg Multiplicative.ofAdd
    exact Subtype.ext (M.period.symm_apply_apply t.toAdd.val)
  right_inv a := Subtype.ext (M.period.apply_symm_apply a.val)
  map_mul' t u := Subtype.ext (M.period_add t.toAdd.val u.toAdd.val)

theorem geometricKernel (k : Type) [Field k] (t : Spec (.of k) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Nonempty (p.isogeny.kernelAt (Over.mk t) ≃*
      Multiplicative ((∀ i : Fin (3 * s), ZMod (P.polarizationType i)) ×
        (∀ i : Fin (3 * s), ZMod (P.polarizationType i)))) := by
  let labels := (AddEquiv.toMultiplicative (F.latticeKernel_type hP).some.symm).trans
    p.complexKernelEquiv
  exact ⟨(RepresentationTheory.Theta.Geometric.IsogenyKernelLabels.isogenyKernel_geometric_labels p.isogeny _ labels k t).some.symm⟩

end ReferenceLatticeIsogeny

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyKernel
