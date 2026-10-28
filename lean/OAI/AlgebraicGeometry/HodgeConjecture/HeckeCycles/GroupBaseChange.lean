import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Group Base Change -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM

noncomputable section

/-! Group-preserving coherence of actual base change requires only the
group object, with no projective presentation or dimension hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

variable {S T U : Scheme} (G : CommGrp (Over S))

def changedGroup (f : T ⟶ S) : CommGrp (Over T) :=
  AbelianScheme.TateComparison.BaseChange.baseChangedGroup G.X f

def compGroupIso (f : U ⟶ T) (h : T ⟶ S) :
    (changedGroup G (f ≫ h)).toGrp ≅
      (changedGroup (changedGroup G h) f).toGrp :=
  (Functor.mapGrpNatIso (Over.pullbackComp f h)).app G.toGrp ≪≫
    (Functor.mapGrpCompIso (F := Over.pullback h) (G := Over.pullback f)).app G.toGrp

def factorGroupIso (f : U ⟶ T) (h : T ⟶ S) (b : U ⟶ S) (w : f ≫ h = b) :
    (changedGroup G b).toGrp ≅
      (changedGroup (changedGroup G h) f).toGrp :=
  (eqToIso (congrArg (fun z => (changedGroup G z).toGrp) w)).symm ≪≫
    compGroupIso G f h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GroupBaseChange.CM
