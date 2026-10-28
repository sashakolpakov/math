import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.OpenQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.PresheafGlobalAugmentation

/-! # Global Cone Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.GlobalConeQuasiIso

noncomputable section

/-! Normalize a genuine global level cone before applying canonical
Ext/global/open section detection. The equality transport is performed
before specializing the coefficient and frame functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z r
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {D : Type r} [SemilatticeInf D]
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

local instance constZero : (Functor.const Dᵒᵖ : ModuleCat.{max w z} R ⥤
    Dᵒᵖ ⥤ ModuleCat.{max w z} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable (ψ : Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ) ⋙
    (Functor.const Dᵒᵖ).mapHomologicalComplex (.up ℕ) ⟶ P ⋙ G.mapHomologicalComplex (.up ℕ))
  (hψ : OpenTotal.transformation.{u,v,w,z,r,r} R J F G e b Q P a = ψ)
  (h : QuasiIso (Cech.PresheafGlobalAugmentation.map R U
    (Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ))
    (P ⋙ G.mapHomologicalComplex (.up ℕ)) ψ))

include hψ h in
theorem quasiIso :
    QuasiIso (Presheaf.ConeQuasiIso.map (A := ModuleCat.{max w z} R) U
      (OpenTotal.sectionMap.{u,v,w,z,r,r} R J F G e b
        (GeometricComparison.CechCone.Total.CechConeTotal.total U Q) (GeometricComparison.CechCone.Total.CechConeTotal.total U P)
        (GeometricComparison.CechCone.TotalLevelMap.CechConeTotalLevelMap.map (constantSheaf J (ModuleCat.{w} R)) U Q P a))) := OpenQuasiIso.quasiIso.{u,v,w,z,r,r} R J F G e b U Q P a
  (Eq.mpr (congrArg (fun θ => QuasiIso (Cech.PresheafGlobalAugmentation.map R U
    (Q ⋙ (ModuleCat.uliftFunctor.{z,w} R).mapHomologicalComplex (.up ℕ))
    (P ⋙ G.mapHomologicalComplex (.up ℕ)) θ)) hψ) h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.GlobalConeQuasiIso
