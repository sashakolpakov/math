import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.HomExtension

/-! # Neron Specialization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization.CM

noncomputable section

/-! HomExtension identifies the integral endomorphism ring with the endomorphisms
of its generic fiber. Reduction therefore defines a genuine ring map,
rather than a separately assumed specialization operation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (G : CommGrp (Over (Spec (.of R))))
  [Smooth G.X.hom] [IsProper G.X.hom] [GeometricallyConnected G.X.hom]

abbrev genericBase : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

def genericRestriction :
    AbelianScheme.TateComparison.End.IntegralEnd G.X →+* AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup G (genericBase (R := R) (K := K))).X :=
  AbelianScheme.TateComparison.BaseChange.endBaseChange G.X (genericBase (R := R) (K := K))

theorem genericRestriction_bijective :
    Function.Bijective (genericRestriction (K := K) G) := by
  let Gη := GroupBaseChange.CM.changedGroup G (genericBase (R := R) (K := K))
  constructor
  · intro f g h
    have hfη : IsMonHom (AbelianScheme.TateComparison.End.endSchemeMap Gη.X (genericRestriction G f)) :=
      AbelianScheme.TateComparison.End.endSchemeMap_isMonHom Gη.X (genericRestriction G f)
    obtain ⟨u, _hu, huniq⟩ := AbelianScheme.HomExtension.neron_extension_of_abelian_hom
      (K := K) G.X G.X (AbelianScheme.TateComparison.End.endSchemeMap Gη.X (genericRestriction G f)) hfη
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective G.X
    have hf : AbelianScheme.TateComparison.End.endSchemeMap G.X f = u := huniq _ ⟨inferInstance,
      (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G.X (genericBase (R := R) (K := K)) f).symm⟩
    have hg : AbelianScheme.TateComparison.End.endSchemeMap G.X g = u := huniq _ ⟨inferInstance, by
      have he := congrArg (AbelianScheme.TateComparison.End.endSchemeMap Gη.X) h
      exact (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G.X (genericBase (R := R) (K := K)) g).symm.trans he.symm⟩
    exact hf.trans hg.symm
  · intro f
    have hfη : IsMonHom (AbelianScheme.TateComparison.End.endSchemeMap Gη.X f) := AbelianScheme.TateComparison.End.endSchemeMap_isMonHom Gη.X f
    obtain ⟨u, hu, _huniq⟩ := AbelianScheme.HomExtension.neron_extension_of_abelian_hom
      (K := K) G.X G.X (AbelianScheme.TateComparison.End.endSchemeMap Gη.X f) hfη
    let : IsMonHom u := hu.1
    refine ⟨AbelianScheme.TateComparison.End.endOfSchemeMap G.X u, ?_⟩
    apply AbelianScheme.TateComparison.End.endSchemeMap_injective Gη.X
    exact (AbelianScheme.TateComparison.BaseChange.endBaseChange_schemeMap G.X (genericBase (R := R) (K := K))
      (AbelianScheme.TateComparison.End.endOfSchemeMap G.X u)).trans
        ((congrArg ((Over.pullback (genericBase (R := R) (K := K))).map)
          (AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap G.X u)).trans hu.2)

def genericEndEquiv :
    AbelianScheme.TateComparison.End.IntegralEnd G.X ≃+* AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup G (genericBase (R := R) (K := K))).X :=
  RingEquiv.ofBijective (genericRestriction G) (genericRestriction_bijective G)

def specialization {k : Type} [Field k] (res : R →+* k) :
    AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup G (genericBase (R := R) (K := K))).X →+*
      AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup G (Spec.map (CommRingCat.ofHom res))).X :=
  (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X (Spec.map (CommRingCat.ofHom res))).comp
    (genericEndEquiv G).symm.toRingHom

theorem specialize_restriction {k : Type} [Field k] (res : R →+* k)
    (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    specialization (K := K) G res (genericRestriction G f) =
      AbelianScheme.TateComparison.BaseChange.endBaseChange G.X (Spec.map (CommRingCat.ofHom res)) f := by
  exact congrArg (AbelianScheme.TateComparison.BaseChange.endBaseChange G.X (Spec.map (CommRingCat.ofHom res)))
    ((genericEndEquiv (K := K) G).symm_apply_apply f)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeronSpecialization.CM
