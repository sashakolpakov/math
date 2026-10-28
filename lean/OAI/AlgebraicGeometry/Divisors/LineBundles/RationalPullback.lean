import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.FunctionField
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary

/-! # Rational Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-!
# LineBundleCycles: actual unit representatives on support deformations

Pullback along the constructed dominant projection takes an actual
nonempty unit open to its actual nonempty inverse image. The resulting
principal divisor is supported over the complement of that original
unit open, by its local orders of vanishing.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

section

variable {A B : Scheme} [IsIntegral A] [IsIntegral B] {g : B.functionField}

/-- Pull back a genuine unit representative along a surjective morphism. -/
def RationalBoundary.BundleCycles.RationalUnitRepresentative.pullback (D : RationalBoundary.BundleCycles.RationalUnitRepresentative B g) (i : A ⟶ B) (hi : Function.Surjective i) :
    RationalBoundary.BundleCycles.RationalUnitRepresentative A
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective i hi) g) := by
  have hn : Nonempty (i ⁻¹ᵁ D.domain) := by
    obtain ⟨x⟩ := D.nonempty_domain
    obtain ⟨y, hy⟩ := hi x.1
    exact ⟨⟨y, (congrArg (fun z => z ∈ D.domain) hy).mpr x.2⟩⟩
  refine { domain := i ⁻¹ᵁ D.domain
           nonempty_domain := hn
           unit := Units.map (i.app D.domain).hom.toMonoidHom D.unit
           represents := ?_ }
  have h := ConcreteCategory.congr_hom
    (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn i (Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective i hi) D.domain)
    (D.unit : Γ(B, D.domain))
  exact h.symm.trans
    (congrArg (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (Deformation.FunctionField.BundleCycles.genericPoint_eq_of_surjective i hi)) D.represents)

@[simp]
theorem RationalBoundary.BundleCycles.RationalUnitRepresentative.pullback_domain (D : RationalBoundary.BundleCycles.RationalUnitRepresentative B g) (i : A ⟶ B)
    (hi : Function.Surjective i) : (D.pullback i hi).domain = i ⁻¹ᵁ D.domain := rfl

end

variable {X : Scheme} (I P : X.IdealSheafData) [IsIntegral P.subscheme]
    {g : P.subscheme.functionField}

/-- The original rational function's unit representative on the actual support deformation. -/
def RationalPullback.BundleCycles.globalSupportRationalRepresentative (D : RationalBoundary.BundleCycles.RationalUnitRepresentative P.subscheme g) :
    RationalBoundary.BundleCycles.RationalUnitRepresentative (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (Deformation.FunctionField.BundleCycles.globalSupportFunctionFieldMap I P g) :=
  D.pullback (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) (Support.Projection.BundleCycles.globalSupportDeformationToSupport_surjective I P)

/-- No divisor coefficient occurs over the original unit domain. -/
theorem RationalPullback.BundleCycles.globalSupportPulledDivisor_vanishes [AlgebraicGeometry.IsNoetherian X]
    (D : RationalBoundary.BundleCycles.RationalUnitRepresentative P.subscheme g) (x : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)
    (hx : Support.Projection.BundleCycles.globalSupportDeformationToSupport I P x ∈ D.domain) :
    (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).ord (Deformation.FunctionField.BundleCycles.globalSupportFunctionFieldMap I P g) x = 0 :=
  (RationalPullback.BundleCycles.globalSupportRationalRepresentative I P D).ord_eq_zero x hx

/-- The complete finite divisor is supported over the complement of the original unit open. -/
theorem RationalPullback.BundleCycles.globalSupportPulledDivisor_support [AlgebraicGeometry.IsNoetherian X]
    (D : RationalBoundary.BundleCycles.RationalUnitRepresentative P.subscheme g) :
    ((Ord.BundleCycles.principalDivisor (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (Deformation.FunctionField.BundleCycles.globalSupportFunctionFieldMap I P g)).support :
      Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) ⊆
      (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) ⁻¹' (D.domain : Set P.subscheme)ᶜ :=
  (RationalPullback.BundleCycles.globalSupportRationalRepresentative I P D).principalDivisor_support_subset

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
