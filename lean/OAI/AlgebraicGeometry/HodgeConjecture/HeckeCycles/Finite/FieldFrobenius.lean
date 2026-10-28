import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndTransportCM
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius

/-! # Field Frobenius -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

/-! Frobenius is the actual power map over the finite residue field.
Its geometric action is obtained by the same faithful base change as
the specialized Hecke endomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM

variable {k L : Type} [Field k] [Fintype k] [Field L]
  (G : CommGrp (Over (Spec (.of k))))

def integralFrobenius : AbelianScheme.TateComparison.End.IntegralEnd G.X :=
  AbelianScheme.TateComparison.End.endOfSchemeMap G.X (FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k G.X)

theorem integralFrobenius_commutes (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    Commute (integralFrobenius G) f := by
  apply AbelianScheme.TateComparison.End.endSchemeMap_injective G.X
  rw [AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul, AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul]
  change AbelianScheme.TateComparison.End.endSchemeMap G.X f ≫ AbelianScheme.TateComparison.End.endSchemeMap G.X (integralFrobenius G) =
    AbelianScheme.TateComparison.End.endSchemeMap G.X (integralFrobenius G) ≫ AbelianScheme.TateComparison.End.endSchemeMap G.X f
  rw [show AbelianScheme.TateComparison.End.endSchemeMap G.X (integralFrobenius G) = FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k G.X from
    AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap G.X _]
  exact (FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius_naturality k G.X (AbelianScheme.TateComparison.End.endSchemeMap G.X f)).symm

theorem integralFrobenius_image_commutes {A : Type*} [Ring A]
    (ρ : AbelianScheme.TateComparison.End.IntegralEnd G.X →+* A) (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    Commute (ρ (integralFrobenius G)) (ρ f) :=
  (integralFrobenius_commutes G f).map ρ

variable (σ : k →+* L)

def geometricEndAction :
    AbelianScheme.TateComparison.End.IntegralEnd G.X →+* AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup G (Spec.map (CommRingCat.ofHom σ))).X :=
  AbelianScheme.TateComparison.BaseChange.endBaseChange G.X (Spec.map (CommRingCat.ofHom σ))

omit [Fintype k] in
theorem geometricEndAction_injective : Function.Injective (geometricEndAction G σ) :=
  EndTransportCM.CM.endBaseChange_injective_field σ G.X

omit [Fintype k] in
theorem transported_geometricEndAction_injective
    (H : CommGrp (Over (Spec (.of L))))
    (e : (GroupBaseChange.CM.changedGroup G (Spec.map (CommRingCat.ofHom σ))).X ≅ H.X)
    [IsMonHom e.hom] :
    Function.Injective ((EndTransportCM.CM.transport e).toRingHom.comp
      (geometricEndAction G σ)) :=
  (EndTransportCM.CM.transport e).injective.comp (geometricEndAction_injective G σ)

def transportedGeometricEndAction
    (H : CommGrp (Over (Spec (.of L))))
    (e : (GroupBaseChange.CM.changedGroup G (Spec.map (CommRingCat.ofHom σ))).X ≅ H.X)
    [IsMonHom e.hom] :
    {ρ : AbelianScheme.TateComparison.End.IntegralEnd G.X →+* AbelianScheme.TateComparison.End.IntegralEnd H.X // Function.Injective ρ} :=
  ⟨(EndTransportCM.CM.transport e).toRingHom.comp (geometricEndAction G σ),
    transported_geometricEndAction_injective G σ H e⟩

def geometricFrobenius :
    AbelianScheme.TateComparison.End.IntegralEnd (GroupBaseChange.CM.changedGroup G (Spec.map (CommRingCat.ofHom σ))).X :=
  geometricEndAction G σ (integralFrobenius G)

theorem geometricFrobenius_commutes (f : AbelianScheme.TateComparison.End.IntegralEnd G.X) :
    Commute (geometricFrobenius G σ) (geometricEndAction G σ f) :=
  (integralFrobenius_commutes G f).map (geometricEndAction G σ)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM.GroupEndAction

/-! Faithful geometric endomorphism transport through a complete group
isomorphism, retaining its homomorphism proof inside the construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

variable {k L : Type} [Field k] [Field L]
  (A : CommGrp (Over (Spec (.of k)))) (σ : k →+* L)
  (B : CommGrp (Over (Spec (.of L))))
  (g : (GroupBaseChange.CM.changedGroup A (Spec.map (CommRingCat.ofHom σ))).toGrp ≅ B.toGrp)

def embedding : {ρ : AbelianScheme.TateComparison.End.IntegralEnd A.X →+* AbelianScheme.TateComparison.End.IntegralEnd B.X // Function.Injective ρ} := by
  let e : (GroupBaseChange.CM.changedGroup A (Spec.map (CommRingCat.ofHom σ))).X ≅ B.X :=
    (Grp.forget _).mapIso g
  let : IsMonHom e.hom := g.hom.hom.isMonHom_hom
  exact transportedGeometricEndAction A σ B e

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM.GroupEndAction

end

end OAI
