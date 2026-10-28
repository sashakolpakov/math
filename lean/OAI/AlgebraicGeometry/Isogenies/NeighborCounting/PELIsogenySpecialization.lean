import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MarkingBaseChange
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange

/-! # PEL Isogeny Specialization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELIsogenySpecialization

noncomputable section

/-! The original generic PEL equations determine the special PEL
isogeny between the independently chosen good models. No comparison of
their special polarizations, actions, or ordered markings is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralMarking
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MarkingBaseChange OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent

variable {R K O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] [CommRing O]
variable {d N n : ℕ} {A B : AbelianScheme.TateComparison.PEL.PELFamilyData O d N (Spec (.of R))}
variable (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.abelian B.abelian)
variable (g : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback (IntegralComparison.genericMap (R := R) (K := K)))
  (B.pullback (IntegralComparison.genericMap (R := R) (K := K))) n)
variable (hf : (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map f.hom = g.isogeny.hom)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
include hf in
theorem generic_native_dual :
    (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map
      (AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.dual B.dual) = g.dualHom := by
  have hD : g.dualHom = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap
      (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap (IntegralComparison.genericMap (R := R) (K := K)) f.hom)
      (A.dual.pullback (IntegralComparison.genericMap (R := R) (K := K)))
      (B.dual.pullback (IntegralComparison.genericMap (R := R) (K := K))) := by
    apply AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (g.dualHom ⊗ₘ 𝟙 _).left _ =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
        (𝟙 _ ⊗ₘ (Over.pullback (IntegralComparison.genericMap (R := R) (K := K))).map f.hom).left _
    rw [hf]
    exact g.poincare.symm
  exact (AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange (IntegralComparison.genericMap (R := R) (K := K))
    f.hom A.dual B.dual).trans hD.symm

omit [IsDiscreteValuationRing R] in
include g hf in
theorem integral_polarization :
    f.hom ≫ B.polarizationMap.hom ≫ AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom A.dual B.dual =
      A.polarizationMap.hom ^ n := by
  apply IntegralComparison.polarization_equation_extends (K := K)
  rw [generic_native_dual f g hf, hf]
  exact g.polarization

omit [IsDiscreteValuationRing R] in
include g hf in
theorem integral_action (a : O) :
    AbelianScheme.TateComparison.End.endSchemeMap A.abelian.scheme (A.action a) ≫ f.hom =
      f.hom ≫ AbelianScheme.TateComparison.End.endSchemeMap B.abelian.scheme (B.action a) := by
  apply IntegralComparison.action_equation_extends (K := K)
  rw [hf, ← A.pullback_action_schemeMap, ← B.pullback_action_schemeMap]
  exact g.equivariant a

variable (hnN : Nat.Coprime n N)
variable (hkernel : ∀ (T : Over (Spec (.of R))) (a : T ⟶ A.abelian.scheme),
  a ≫ f.hom = 1 → a ^ n = 1)

omit [IsDiscreteValuationRing R] in
include g hf hnN hkernel in
theorem integral_marking (T : Over (Spec (.of R)))
    (c : LocallyConstant T.left (Multiplicative (Fin (2 * d) → ZMod N))) :
    (A.marking.hom.app (.op T) c).val ≫ f.hom = (B.marking.hom.app (.op T) c).val :=
  IntegralMarking.marking_transport_from_generic f hnN hkernel A.marking B.marking
    (MarkingBaseChange.generic_marking_on_constant_sections f g hf) T c

variable {k : Type} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of R))

/-- The special source and target retain their original PEL data. The
dual comes from Picard pullback and its normalized Poincare equation. -/
def specialPELIsogeny : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny (A.pullback s) (B.pullback s) n where
  isogeny := f.pullback s
  dualHom := AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap s f.hom)
    (A.dual.pullback s) (B.dual.pullback s)
  dualGroup := inferInstance
  poincare := by
    rw [← Intrinsic.DualIdentification.dualMap_eq_native]
    simp only [id_tensorHom, tensorHom_id]
    exact PoincareDescent.poincareClass_eq (A.dual.pullback s) (B.dual.pullback s)
      (AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap s f.hom)
  polarization := by
    have h := congrArg (Over.pullback s).map (integral_polarization f g hf)
    rw [Functor.map_comp, Functor.map_comp, AbelianScheme.TateComparison.PELBaseChange.pullback_map_pow,
      AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange] at h
    exact h
  equivariant a := by
    rw [A.pullback_action_schemeMap, B.pullback_action_schemeMap]
    exact ((Over.pullback s).map_comp _ _).symm.trans
      ((congrArg (Over.pullback s).map (integral_action f g hf a)).trans
        ((Over.pullback s).map_comp _ _))
  marking T c := by
    apply (B.abelian.baseChangePointsEquiv s T).injective
    exact (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map f.hom s T
      ((A.marking.pullback s).hom.app (.op T) c).val).trans
        ((congrArg (fun z => z ≫ f.hom) (AbelianScheme.TateComparison.PELBaseChange.fullLevel_pullback_basis A.marking s T c)).trans
          ((integral_marking f g hf hnN hkernel ((Over.map s).obj T) c).trans
            (AbelianScheme.TateComparison.PELBaseChange.fullLevel_pullback_basis B.marking s T c).symm))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PELIsogenySpecialization
