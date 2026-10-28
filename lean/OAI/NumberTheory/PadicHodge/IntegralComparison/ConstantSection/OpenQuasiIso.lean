import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeQuasiIso

/-! # Open Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenQuasiIso

noncomputable section

/-! The original constant-sheaf global-section map has a quasi-isomorphic
open Čech augmentation whenever its actual level-section cone does.
Both coefficient coordinate maps are genuine canonical isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z r s
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D : Type r} [Category.{s} D] [HasBinaryProducts D]
  (F : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max w z} R) [F.Additive]
  (G : Sheaf J (ModuleCat.{w} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max w z} R) [G.Additive]
  (e : Ext.ModuleFunctor.functor R (Module.ConstantSections.constantUnit R J) 0 ⟶ F)
  (b : F ⋙ Functor.const Dᵒᵖ ⟶ G)
  [HasProducts.{0} (Sheaf J (ModuleCat.{w} R))]
  [HasCoproducts.{0} (Sheaf J (ModuleCat.{w} R))]
  {ι : Type} [Finite ι] (U : ι → D)
  (Q : Dᵒᵖ ⥤ CochainComplex (ModuleCat.{w} R) ℕ)
  (P : Dᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : Q ⋙ (constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ) ⟶ P)

local notation "V" => Functor.const Dᵒᵖ
local notation "S" => constantSheaf J (ModuleCat R)
local notation "θ" => OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenTotal.transformation R J F G e b Q P a

local instance openQuasiIsoWeakSheafify : HasWeakSheafify J (ModuleCat.{w} R) :=
  HasSheafify.isRightAdjoint

local instance constZero : (Functor.const Dᵒᵖ : ModuleCat.{max w z} R ⥤
    Dᵒᵖ ⥤ ModuleCat.{max w z} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def level := GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map V U
  (Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ))
  (P ⋙ G.mapHomologicalComplex (.up ℕ)) θ

theorem quasiIso (h : QuasiIso (Presheaf.ConeQuasiIso.map (A := ModuleCat.{max w z} R) U (level.{u,v,w,z,r,s} R J F G e b U Q P a))) :
    QuasiIso (Presheaf.ConeQuasiIso.map (A := ModuleCat.{max w z} R) U
      (OpenTotal.sectionMap.{u,v,w,z,r,s} R J F G e b
        (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) (GeometricComparison.CechCone.Total.CechConeTotal.total U P)
        (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map S U Q P a))) :=
  Presheaf.ConeQuasiIso.quasiIso (A := ModuleCat.{max w z} R) U
    (OpenTotal.sectionMap.{u,v,w,z,r,s} R J F G e b
      (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) (GeometricComparison.CechCone.Total.CechConeTotal.total U P)
      (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map S U Q P a)) (level.{u,v,w,z,r,s} R J F G e b U Q P a)
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso (ModuleCat.uliftFunctor.{z,w} R) U Q)
    (GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso G U P)
    (OpenTotal.total.{u,v,w,z,r,s} R J F G e b Q P a U) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenQuasiIso
