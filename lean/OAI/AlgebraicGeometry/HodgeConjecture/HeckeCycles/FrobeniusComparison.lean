import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison

/-! # Frobenius Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusComparison.CM

noncomputable section

/-! The canonical power-map Frobenius is preserved by every actual
isomorphism over the residue field and is the same algebraic endomorphism
used by GeometricComparison/Completion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FieldFrobenius.CM

variable {k : Type} [Field k] [Fintype k]
  (G H : CommGrp (Over (Spec (.of k))))

theorem integralFrobenius_schemeMap :
    AbelianScheme.TateComparison.End.endSchemeMap G.X (Finite.FieldFrobenius.CM.integralFrobenius G) = FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius k G.X :=
  AbelianScheme.TateComparison.End.endSchemeMap_ofSchemeMap G.X _

theorem transport_integralFrobenius (e : G.X ≅ H.X) [IsMonHom e.hom] :
    EndTransportCM.CM.transport e (Finite.FieldFrobenius.CM.integralFrobenius G) = Finite.FieldFrobenius.CM.integralFrobenius H := by
  apply AbelianScheme.TateComparison.End.endSchemeMap_injective H.X
  rw [EndTransportCM.CM.transport_schemeMap, integralFrobenius_schemeMap,
    integralFrobenius_schemeMap, FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius_naturality,
    Iso.inv_hom_id_assoc]

theorem integralEquiv_frobenius :
    EndomorphismComparison.CM.integralEquiv G.X (Finite.FieldFrobenius.CM.integralFrobenius G) =
      FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k G.X := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact integralFrobenius_schemeMap G

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusComparison.CM
